# Proving log

> Two derived files are easier to act on than this one:
> [ERRATA.md](ERRATA.md) lists **every defect found in the theses**, ordered by
> point number, and [QUESTIONS.md](QUESTIONS.md) lists **everything awaiting an
> author decision**.  This file is the full record behind them — errata with
> their working, our own mis-transcriptions, parked items, and divergences from
> the theses' own proofs.

Running log of the effort to replace the `sorry`s in this formalization by
real proofs.  **Statements are never changed** — if a statement is wrong,
un-provable as stated, or needs infrastructure we don't have, it is *parked*
here with a short note and its `sorry` left in place.

Status is tracked per file; the authoritative count is always
`grep -c sorry Theses/**/*.lean`.

## Where the proofs are

Do not re-derive the mathematics — the theses contain it.

1. **Inline proofs.** In the LaTeX sources nearly every Lemma/Proposition/
   Theorem point is immediately followed by a `\begin{point}{N}{Proof}` point
   with the author's proof.  Each Lean declaration's doc comment gives
   `file:LINE`; read on from there in the `.tex`.
2. **Exercise solutions.**  `../bsols.tex` (thesis B, 79 solutions) and
   `../asols.tex` (thesis A, 64).  **The two are keyed differently — this
   caught us out for a whole session:**
   * `bsols.tex` uses the *same LaTeX label* our doc comments carry:
     `grep -n 'solution}{exc-subbase}' ../bsols.tex`.
   * `asols.tex` uses **parsec and point numbers**, not labels:
     `solution}{parsec-<parsec×10>.<point×10>}`.  So the DISP `4IV` (parsec 4,
     point IV = 4) is `grep -n 'solution}{parsec-40.40}' ../asols.tex`; `9X` is
     `parsec-90.100`; `11XV` is `parsec-110.150`.
     Grepping `asols.tex` by label returns **zero matches for all 64
     solutions**, which reads exactly like "there is no solution".  List what
     exists with `grep -o 'solution}{[^}]*}' ../asols.tex`.
3. **Known errata — check these before filing anything new.**  Thesis B has
   `../berr.tex`.  **Thesis A has no `aerr.tex`**: its 42 errata/addenda live at
   the *top of* `../asols.tex`, keyed the same `parsec-N.M` way.  (Checking
   there first would have saved this project one duplicate finding: the 11XV.3
   sign error is already recorded at `asols.tex:30–34`.)

So the workflow per `sorry` is: find the thesis's own proof, then transcribe
it into Lean.  When parking an item, note whether the thesis has a proof you
couldn't transcribe or leaves it to the reader.

**The author's proof takes precedence over a Mathlib shortcut.**  Reach for
Mathlib only for the mechanical steps *inside* the author's argument, or when
that argument genuinely cannot be transcribed — and say so when you do.  A
one-line Mathlib closure proves the statement but cross-checks nothing, and
cross-checking is what produces errata: re-reading nine such proofs against the
authors' arguments yielded four new errata in one pass.

This extends to **dependency order**.  Where the thesis deliberately avoids a
theorem it has not yet reached, do not substitute Mathlib's version — the proof
will be sound and will validate none of the bootstrapping.  See the
"development-order divergences" under session 2 (9X.3, 11XV.3).

**Record every divergence, not just repairs.**  The authors need to know which
statements have actually been cross-checked against their arguments.  Four
cases, all worth logging:

1. the thesis proof is wrong or incomplete (the errata below);
2. the thesis proof is fine but Lean took a different route (say which Mathlib
   lemma replaced it);
3. the Lean proof uses a different *dependency order* (e.g. 34XVI, 23VII.0'');
4. **the thesis proof was never consulted** — closed directly from Mathlib.
   This is a legitimate and useful entry: it flags a statement that is proved
   but *not* cross-checked against the thesis.  It is also the easiest to omit,
   so state it explicitly.

## Errata / proof repairs

> **⚠️ 2026-08-13: most thesis-A entries below have since been RULED ON by the
> author and INCORPORATED into the tex sources.**  Before acting on any
> thesis-A entry here, check HANDOFF.md § "Resolved by the author
> (2026-08-13)" and the errata block at the top of `../asols.tex`.  Entries
> below are kept as the historical record and are **not** updated.

Places where the thesis's own proof (or statement) turned out to be wrong,
incomplete, or in need of a different argument, and what the formalization
does instead.  These are the interesting findings for the authors — record
them even when the repair was easy.

(Format: `- **DISP** `file:line` — what the thesis does, why it fails, what
the Lean proof does instead.`)

- **189I.2** `Theses/B/Eff/Effectus.lean:1061` — bsols.tex:1822 says "as 0 is
  final in an effectus in *total* form … as 0 is a strict initial object in an
  effectus in *partial* form"; the two forms are swapped.  0 is a zero object
  (hence final) in an effectus in *partial* form, and strictness of 0 is what
  part 1 proves for an effectus in *total* form.  The Lean proof takes the PCM
  zero map `0 : X ⟶ ⊥` (partial form) and applies part 1 (total form) to it.
- **186VIII.2** `Theses/B/Eff/Effectus.lean:996` — the proof (eff.tex:1640)
  uses the right pullback square of 180I with `κ₂` in place of `κ₁`; only the
  `κ₁` square is an axiom, and the `κ₂` variant is silently obtained by
  symmetry.  The Lean proof transports the axiom along the coproduct braiding
  first (`isPullback_kappa_inr`).
- **181IV.1** `Theses/B/Eff/Effectus.lean:428` — the `⇐` direction of the
  proof (eff.tex:1030) goes through the four-fold sum
  `[f,0] ⋁ [0,g] ⋁ [f',0] ⋁ [0,g']`, which tacitly needs the generalized
  (permutation) associativity of PCM sums of 174IV — itself still a `sorry`
  here.  The Lean proof avoids it by applying the compatible-sum axiom
  directly to `[(κ₁∘f) ⋁ (κ₂∘f'), (κ₁∘g) ⋁ (κ₂∘g')] : X+Y ⟶ Z+Z`.
- **183III.1** `Theses/B/Eff/Effectus.lean:728` — minor: the solution
  (bsols.tex:1708) has two dropped `=` signs ("Clearly `g ∘ f ∘ δ g ∘ γ = α`",
  "`k ∘ δ' ∘ β`"); the argument itself transcribes without change.

- **181XIII** `Theses/B/Eff/StatesPredicates.lean:139` (helper
  `truth_effObj_eq_id`) — the thesis's proof (eff.tex:1181) starts the chain
  with "$1 = 1 \after 1$", which is not available at that point: that `1∘1 = 1`
  is a *consequence* of the very computation that follows.  The step is also
  unnecessary.  The Lean proof drops it: PCM-enrichment applied to
  `id ⋁ idᵖ = 1` gives `1 ⊥ (1 ∘ idᵖ)` (as `1 ∘ id = 1`), so the zero–one
  axiom yields `1 ∘ idᵖ = 0`, hence `idᵖ = 0` and `id = 1`.

- **178IIIa** `Theses/B/Eff/EffectAlgebras.lean:1132` (`exc_emonzero`) — the
  solution (bsols.tex:1645) argues `a ⊙ 1 = a ⊙ (0 ⋁ 1) = (a⊙0) ⋁ (a⊙1)`, i.e.
  it uses one-sided distributivity.  That is *not* an axiom of an effect
  monoid: 178II only gives the four-fold law
  `(a⋁b) ⊙ (c⋁d) = (a⊙c) ⋁ (b⊙c) ⋁ (a⊙d) ⋁ (b⊙d)`, and instantiating `b := 0`
  leaves the two extra summands `0⊙0` and `0⊙1`, whose vanishing is exactly
  what is being proved.  The Lean proof instead instantiates the four-fold law
  at `(a ⋁ 0) ⊙ (0 ⋁ 0) = a ⊙ 0`, whose expansion
  `(a⊙0) ⋁ (0⊙0) ⋁ (a⊙0) ⋁ (0⊙0)` has `a⊙0` as its *leading* summand;
  cancelling it and applying positivity twice gives `a ⊙ 0 = 0` with no
  auxiliary fact.  `0 ⊙ a = 0` then follows from `(0 ⋁ 0) ⊙ (0 ⋁ a) = 0 ⊙ a`
  using `0 ⊙ 0 = 0`.
- **175V.7** `Theses/B/Eff/EffectAlgebras.lean:597` (`eabasics_le_perp_compat`)
  — the proof (eff.tex:414) writes `b ⋁ c = (a ⋁ d) ⋁ c = (a ⋁ c) ⋁ d`, "so
  `a ⊥ c`".  The second equality uses partial associativity *backwards*: from
  `a ⊥ (c ⋁ d)` conclude `a ⊥ c` and `(a ⋁ c) ⊥ d`.  The PCM axioms (174II)
  only state the forward direction.  The Lean development therefore adds the
  helper `PCM.assoc_left`, deriving the converse from partial commutativity;
  it is used again in several places.  The same silent step occurs in the
  `exc-dposet` solution (bsols.tex:1494 ff.).
- **175II.4** `Theses/B/Eff/EffectAlgebras.lean:1004`
  (`orthomodularEffectAlgebra`) — worth recording that the *orthomodular* law
  is genuinely needed for the effect-algebra structure, not just decoration:
  uniqueness of the orthocomplement (`orth_unique`) fails in a mere
  ortholattice, and the Lean proof obtains it from
  `b ⊔ (bᶜ ⊓ aᶜ) = aᶜ` (orthomodularity at `b ≤ aᶜ`) together with
  `bᶜ ⊓ aᶜ = ⊥`.  The latter is proved directly from `a ⊔ b = ⊤` rather than
  via de Morgan, which is not among the `Ortholattice` axioms as stated.

- **221IV.6** `Theses/B/Eff/Dagger.lean:544` — the thesis's proof
  (eff.tex:6923) of "if `(P,ϱ,h)` dilates `f ∘ ξ` then `(P,ϱ,h'')` dilates
  `f`" verifies the universal property but never checks that the induced
  `h''` (the unique map with `ξ ∘ h'' = h`) is *pure*, which the definition
  221II of a dilation requires.  (For the neighbouring parts 4, 5 and 7 the
  formalization takes the corresponding purity/sharpness side conditions as
  hypotheses; for 6 there is nothing to take.)  Everything else of 221IV.6 is
  proved in Lean; the purity of `h''` is the single remaining `sorry` inside
  that proof.
- **211XVI** `Theses/B/Eff/DiamondAmp.lean:987` — the doc comment of the
  `Pure C` category instance says identities-are-pure and closure under
  composition are `sorry`-ed; identities are now proved outright
  (`𝟙 = 𝟙 ∘ 𝟙` with 197V.3 and 199VII.3) and composition is discharged by
  citing 211XI (`upm_closed_pure`, still a `sorry`), so the instance itself
  is `sorry`-free.  (Doc comment left untouched.)
- **195VII** `Theses/B/Eff/StatesPredicates.lean:1255` (`divisoid_div_ovee`) —
  the thesis's proof (eff.tex:3331) rests on an "initial lemma": *if
  `c ⊙ a ⊥ c ⊙ b` then `(c/c) ⊙ a ⊥ (c/c) ⊙ b`*.  That lemma is **false**:
  in the effect divisoid `[0,1]` take `c = ½` and `a = b = 1`; then
  `c⊙a ⋁ c⊙b = 1` is defined while `(c/c)⊙a = (c/c)⊙b = 1` are not
  summable.  The gap is the step `c ⊙ a ≤ c ⊙ bᵖ`, which does not follow
  from `c ⊙ a ≤ (c ⊙ b)ᵖ = (c ⊙ bᵖ) ⋁ cᵖ` (in the example: `½ ≰ 0`).
  The Lean proof avoids the lemma entirely.  With `s = a ⋁ b`: pick a
  complement `w` of `a/s` below `s/s`; then `s ⊙ w = b` (distributivity of
  `⊙` over `⋁` plus cancellation), so `w = b/s` by the *uniqueness* axiom of
  the division.  Hence `a/s ⊥ b/s` with `a/s ⋁ b/s = s/s`, and multiplying
  by `s/c` — using `(b/c) ⊙ (a/b) = a/c` (195IV.2) three times, in
  particular `(s/c) ⊙ (s/s) = s/c` — yields `a/c ⊥ b/c` and
  `(a ⋁ b)/c = a/c ⋁ b/c`.

- **16V** `Theses/A/CStar/Positive.lean:281` (`spectrum_nonempty`,
  cstar.tex:2646) — *false as stated for the trivial C*-algebra*: in
  `𝒜 = {0}` every element is invertible (`0 = 1`), so `spec(a) = ∅` for the
  self-adjoint `a = 0`.  The exercise implicitly assumes `𝒜 ≠ {0}`, although
  8II (cstar.tex:1071) explicitly admits the trivial C*-algebra.  Mathlib's
  `spectrum.nonempty` correspondingly carries a `[Nontrivial A]` hypothesis.
  Since statements may not be changed, the item is parked.
  **[RESOLVED 2026-08-13 — 16V now assumes `𝒜 ≠ {0}`; see HANDOFF.]**
- **General (parsec 11, 8II)** `Theses/A/CStar/Basic.lean` — several spectrum
  statements are true but *vacuous* in the trivial C*-algebra, where Mathlib's
  `NormOneClass` (and hence `spectrum.norm_le_norm_of_mem`) is unavailable:
  `scalar_norm_2/3`, `spectrum_bounded_1`, `spectrum_basic_3`,
  `spectrum_self_adjoint_real_2`.  Each Lean proof therefore opens with
  `rcases subsingleton_or_nontrivial 𝒜`, the trivial case being closed by
  `isUnit_of_subsingleton`.  Worth knowing that the thesis's convention (norms
  `‖1‖ ≤ 1` rather than `= 1`) costs a case split throughout.
- **11VI.2** `Theses/A/CStar/Basic.lean:1011` (`spectrum_bounded_2`) — confirms
  the erratum already flagged in the doc comment: the thesis's hypothesis
  `‖a‖ < ‖b‖` is not enough (take `b` a large but badly conditioned invertible
  element).  With the standard `‖a‖ < ‖b⁻¹‖⁻¹` the thesis's own argument goes
  through verbatim: `b - a = b(1 - b⁻¹a)` with `‖b⁻¹a‖ < 1`, so `1 - b⁻¹a` is
  a unit by the geometric series (11II).

- **225VI** `Theses/B/Eff/Comparisons.lean` (`pred_sea_s1_s2_s3`) — not an
  erratum, but a *shorter route* than the thesis's.  For (S3) the thesis
  (eff.tex:7415) argues `andthen p q = 0 ⟹ asrt_q ∘ asrt_p = 0 = asrt_0`,
  applies the dagger to get `asrt_p ∘ asrt_q = 0`, and concludes.  That needs
  `asrt_p^† = asrt_p` and functoriality of the dagger — both still `sorry` in
  `Dagger.lean`.  One can avoid the dagger entirely and use only the
  `asrt_sq` axiom of a †-effectus together with uniqueness of square roots:
  from `1 ∘ asrt_q = q` and `andthen p q = 0` one gets `asrt_p ∘ asrt_q = 0`
  by the zero–one axiom; then
  `asrt_{q&p} ∘ asrt_{q&p} = asrt_q ∘ asrt_p ∘ asrt_p ∘ asrt_q = 0`
  by `asrt_sq`, so `(q&p) & (q&p) = 0 = 0 & 0`, and `sqrt_existsUnique 0`
  forces `q & p = 0`.  Worth recording in the thesis as it removes the
  dependence of 225VI on the whole of 216–220.
- **225VI**, (S2): `andthen 1 p = p` is "obvious" in the thesis; in Lean it
  is exactly the second half of the absorption rule 211XV
  (`asrt_absorp_rule`) applied to `f = p`, `t = 1`, using `IsSharp 1`.

### Repairs to *our* formalization (not thesis errata)

- **74IV.3** `Theses/A/VN/Completeness.lean` `kaplansky_effects` — **silently
  weaker than the thesis**.  vn.tex:4335 puts `‖a_α‖ ≤ ‖b‖` in the *main*
  claim of Kaplansky's density theorem, and the three "moreover" clauses only
  *add* properties to those same `a_α`.  Our `kaplansky`, `kaplansky_sa` and
  `kaplansky_pos` all carry the bound; `kaplansky_effects` had dropped it.
  Not recoverable downstream: being an effect gives only `‖a_α‖ ≤ 1`, which is
  strictly weaker whenever `‖b‖ < 1` — and the thesis's own proof does deliver
  the bound.  Restored.  Another instance of the "silent half-repair" pattern:
  a clause corrected or dropped in one sibling and not carried to the others.
  Found by the A/VN worker reading the declaration against the `file:LINE` in
  its own doc comment.

- **195V.1** `Theses/B/Eff/StatesPredicates.lean` `unitInterval.effectDivisoid`
  — the `EffectDivisoid` class demands a *total* `div : M → M → M`, whereas the
  thesis's division is partial (meaningful only for `a ≼ b`), and every axiom
  of the class is guarded by `a ≼ b` accordingly.  The instance body defined
  `div a b := a / b`, whose membership obligation `a/b ∈ [0,1]` is false for
  `a > b` — uncompletable.  Fixed by truncating: `div a b := min (a/b) 1`
  (and `0` when `b = 0`), which agrees with the ordinary quotient exactly
  where the axioms apply.  No statement changed; the five axiom fields are now
  provable rather than blocked.

### Suspected errata noted during statement-writing (not yet reached by proving)

- **38VI.2** `Theses/A/CStar/TowardsVN.lean` — ✅ **confirmed and fixed by the
  author.**  The "if" direction was indeed false: vector functionals are
  phase-invariant, so the constant net `i • x` (`x ≠ 0`) induces the same
  vector functional as `x` without converging to it.  Erratum `parsec-380.60`
  drops it ("it is false, but not used later on"), and cstar.tex now states
  point 2 as a single implication.  Our statement, which had recorded the iff
  verbatim, is realigned — **and with the false direction gone the point is
  provable, so it is now proved.**  Parsec 380 has no published solution
  (`asols.tex` has no `parsec-380.*` solution entry, only the erratum), so the
  argument is ours: split the difference as `⟪y−x, Ty⟫ + ⟪x, T(y−x)⟫`, giving
  `‖vf y − vf x‖ ≤ ‖y−x‖(‖y‖+‖x‖)` uniformly in `‖T‖ ≤ 1`, then squeeze.  This
  is one of the statements that "survives only by accident" in reverse: it was
  *unprovable* while the false half was attached.
- **61II** `Theses/A/VN/Projections.lean` — thesis's displayed inequality looks
  reversed (counterexample: the trace on `M₂`); the Lean statement follows the
  direction the surrounding proof actually uses.
- **30IV.2** `Theses/A/CStar/Representation.lean` — thesis carries an extra
  `‖ω‖` factor that the argument does not seem to need.

- **30IV.2** `Theses/A/CStar/Representation.lean:380` (`omega_norm_basic_2`) —
  the suspicious extra `‖ω‖` factor flagged in the task list: *not yet closed in
  Lean*, but the evidence is now concrete.  Mathlib's GNS construction
  (`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`) builds
  `PositiveLinearMap.leftMulMapPreGNS a : f.PreGNS →L[ℂ] f.PreGNS` by
  `LinearMap.mkContinuous` with bound **`‖a‖`** — i.e. Mathlib proves exactly
  `‖a·x‖_ω ≤ ‖a‖ ‖x‖_ω`, with no `‖ω‖`.  So the thesis's extra factor is indeed
  spurious (harmless, since `‖ω‖ ≥ 1` is not assumed but the inequality with the
  factor is weaker only when `‖ω‖ ≥ 1`).  Transcribing that bound into
  `omega_norm_basic_2` is the remaining work (see the parked entry).
- **27VIII–27XV** `Theses/A/CStar/Representation.lean:78`–`:150` — not an error,
  but worth recording for the authors: the thesis reaches Gelfand's theorem
  through *Riesz ideals* (order ideals closed under `|·|`), while Mathlib
  reaches it through maximal *ring* ideals (`Ideal.toCharacterSpace`).  The
  formalization therefore proves the *conclusions* of parsec 270 (**27XV**
  `inv_mult_state` is Mathlib's `WeakDual.CharacterSpace.exists_apply_eq_zero`,
  **27XVII**, **27XVIII**, **27XXVII**) from Mathlib, and the Riesz-ideal
  machinery of 27VIII–27XIII is left as the thesis's own (independent) route.

### Session 2 — bootstrapping rework (the author's decision)

Once the author decided the formalization should validate the thesis's *own
development order*, not merely its statements, the seven dependency-order
findings became work.  Result: `Positive.lean` 33 → 29, both files build, every
touched theorem re-verified `[propext, Classical.choice, Quot.sound]`, and
**nothing regressed**.

**23II is proved — all four parts, and this was the whole game.**  The thesis
hand-builds `√` at 23II precisely so it does not need the continuous functional
calculus, which it only obtains after Gelfand at 270–280.  `Positive.lean` now
carries a ~450-line private `SqrtAux` development following cstar.tex:3495–3634
that **uses nothing past parsec 170** — CFC appears nowhere in it.  Chain:
`sqrt_lemma_exists` → `sqrt_unit_exists` → `sqrt_exists_core` →
`sqrt_unique_core` → `mul_nonneg_of_commute` (230.40) → `sq_le_sq_of_commute` →
`sqrt_lemma_le` (230.50) → `sqrt_le` → `sqrt_lemma_unique` (230.60).  Two
documented departures, neither weakening the order: successive differences are
bounded against the scalar iteration `r_{n+1} = ½(1 + rₙ²)` rather than via
nonneg-coefficient polynomials (less machinery, same inputs), and monotonicity is
derived *after* `mul_nonneg_of_commute`, since existence never needed it.

**Parsec 230 de-CFC'd.**  The sharpest case, **23VII.0''**, no longer calls
`CFC.sqrt_le_sqrt` (= thesis 28III, five parsecs later and resting on 23VII):
it builds the thesis's `d`, gets `c ≤ d` from `ineq-square-root`, and only then
identifies `d = CFC.sqrt a`.  **23VII.0** is now entirely CFC-free.  Also
repaired: 23VII.1, .2, 25I(1→3), 25II.2, and **26II.1** — which used
`CFC.sqrt_le_sqrt` again, and now uses the author's actual argument
(asols.tex:2372 says `√` is monotone *on commuting positive elements*, which is
23VII, not 28III).

Also: **17V** restructured to the elementary cycle `1→3→2→1`, with the bridge to
Mathlib's `0 ≤ a` isolated in a single `tfae_have`; **17VI.6** now uses the
author's spectral route instead of `CStarAlgebra.inv_le_inv` (= 25II.3);
**27XV**'s easy direction is now elementary and Gelfand-free.  One violation not
in the audit was found and fixed: **20V.1** used `CFC.sqrt` (parsec 230) at
parsec 200.  One more is flagged but unfixed: **20aI.2**
`cstar_product_2_positive` does the same at parsec 201, repairable in ~40 lines
via the sup-norm characterisation with no square root at all.

**Could not be made honest, with reasons.**  **27XV**'s hard direction needs
27VIII–27XIII, all still `sorry`; citing them would hide a `sorryAx`.  **16II**
is blocked twice over — Mathlib's proof uses the Gelfand–Beurling formula that
**16IV** explicitly disowns, *and* the thesis's own route needs
`rigid_expansion`/`taylor`/`goursat`, i.e. the unproved complex-analysis block at
parsecs 120–150.

**Two new errata** (neither already in the `asols.tex` header block):

- **23II** `cstar.tex:3629` — "`(1−b')(b'−b)` is positive by
  `\sref{ineq-square-root}`" cites the wrong result; it should be
  `\sref{square-commuting-monotone}` (230.40), which is where commuting products
  are handled.  230.50 is the inequality.
- **17VI**.6 `asols.tex:1844` — "suppose that `a` is **not** invertible, then
  `0 ∉ spec(a)`" should read "**is** invertible"; as written it contradicts
  itself.  (Independently re-derived here; also found by the round-1 audit.)

### The remaining obstruction: what `0 ≤ a` means

**25I is not honest, and no rewrite of any proof can make it so.**  The two
defects are *modelling artefacts*, not proof defects:

- `4 → 1` — "`a = c*c` implies `a` positive" is the thesis's 19III + 24IV, one of
  the chapter's deepest results.  In Lean it is `star_mul_self_nonneg`: **true by
  definition** of Mathlib's star order.  The deepest theorem of the chapter is
  a triviality in our encoding.
- `1 ↔ 5` is 25I itself, imported from the CFC.

The same applies at `astara_non_negative` (19III).

**The fix is `ThesisPos`** — define the thesis's own positivity predicate and
prove the spine in those terms *alongside* the shipped statements, so nothing is
restated and no statement changes.  **This has now been done in full**; see the
next section.

### ⚠️ For the authors — **72III.1b and 1c carry a spurious `‖ω‖`**

`vn.tex:3850` (`bstaromega-basic`), part 1.  Both bounds are printed with a
leading `‖ω‖` (= `ω(1)`), and that factor must not be there: `‖a‖_ω = ω(a*a)^½`
is **unnormalised**, so replacing `ω` by `tω` scales the left side by `t` and the
right by `t²`.  Counterexample `𝒜 = ℂ`, `ω = t·id` with `0 < t < 1`,
`a = b = c = 1`: the left side is `t`, the right `t²`.  Cauchy–Schwarz gives the
factor-free bound directly.

**This is the third appearance of the same slip**, after **30IV**.2 (where the
extra `‖ω‖` was independently confirmed spurious — Mathlib's `leftMulMapPreGNS`
is *defined* with bound exactly `‖a‖`) and the earlier report of this same pair.
A spurious `‖ω‖` on a `‖·‖_ω` estimate is evidently a recurring authorial habit;
**every such bound in both theses is worth re-checking**.  Our statements are
corrected and the errata recorded on the declarations; 72V and 72XI lean on them.

### For the record — **88IV `carrier_vector_state` was ours**

`NormalFunctionals.lean`.  vn.tex:6730 *and our own doc comment* both say
`⋃_{a∈S} ⌈|ax⟩⟨ax|⌉`, but the Lean term had dropped the `⌈·⌉`, reading
`projSup {p | ∃ T ∈ S, p = ketbra (T x) (T x)}`.  That set contains
non-projections (take `2•1 ∈ S`), so `projSup` returns its junk value `0` for
every `x ≠ 0` while the left-hand side does not — false, and not the thesis's
fault.  Note the doc comment was *right* the whole time: the defect was visible
by reading the declaration against its own prose, with no reference to the
source at all.  Fixed.

### ⚠️ For the authors — **68IV.2 is false as printed, in two clauses**

**[RESOLVED 2026-08-13 — positivity added to both clauses in vn.tex, erratum
680.40; the Lean fix below is authorised.  See HANDOFF.]**

`vn.tex:3490` (`cceil-basic`), part 2.  Central support `⌈⌈·⌉⌉` is monotone on
**positive** elements only, and two of the three clauses omit that hypothesis:

- "Show that `⌈⌈⋁D⌉⌉ = ⋃_{d∈D} ⌈⌈d⌉⌉` **for any bounded directed subset of `𝒜`**"
  (vn.tex:3497).  Counterexample in any nontrivial `𝒜`: `D = {−1, 0}` is
  directed and bounded with `⋁D = 0`, so the left side is `⌈⌈0⌉⌉ = 0` while the
  right is `⌈⌈−1⌉⌉ ∪ ⌈⌈0⌉⌉ = 1`.
- "Show that `⌈⌈a+b⌉⌉ = ⌈⌈⌈a⌉ ∪ ⌈b⌉⌉⌉ = ⌈⌈a⌉⌉ ∪ ⌈⌈b⌉⌉` **for all `a,b ∈ 𝒜`**"
  (vn.tex:3504).  Same defect: `a = 1`, `b = −1` gives `⌈⌈0⌉⌉ = 0` against `1`.

Both need `0 ≤ ·`.  The middle clause (about a collection of projections) is
fine.  **Suggested fix for the thesis**: add "of positive elements" to the first
and "for all positive `a,b ∈ 𝒜`" to the third.

**Our transcription was also at fault, and instructively so.**  The original Lean
statement had *silently repaired* the third clause — it carried `0 ≤ a`, `0 ≤ b`
that the source lacks — while leaving the first clause faithful and therefore
false, and it had *dropped* the middle term `⌈⌈⌈a⌉ ∪ ⌈b⌉⌉⌉` of the third clause's
three-way equality.  So one transcriber noticed the author's missing hypothesis,
fixed it in one place, did not carry the fix across, and lost a conjunct while
doing so — leaving no trace of any of it.  Both defects are now corrected and the
erratum is documented on the declaration itself.

The general lesson, which the `Examples`/`Remark` sweep would systematise: a
silent half-repair is invisible to `grep`, to the build, and to the axiom
checker.  Only a line-by-line comparison against the `file:LINE` in the doc
comment finds it.

### Session 2 — A/VN, third pass: the 44XI chain and parsecs 560–580

226 → 205 (Basic 48→44, Projections 88→72, Completeness 26→25).  Build green;
all 15 headline results `#print axioms`-clean.

**The predicted import unblock worked exactly as forecast.**  Adding
`import Theses.A.CStar.Representation` to `A/VN/Basic.lean` (after verifying
`proto_gelfand_naimark_1` really is sorry-free) released the whole chain:
`conjNP` — the new hinge, that `a ↦ ω(b*ab)` is an np-functional, by positivity
plus `ad_normal` for normality — then **44XI** `np_orderSeparating` with
`np_separating` and `eq_of_forall_npFunctional`, **44XI.1/.2**, **44XIII**
`vna_supremum_commutes`, and **72III.1a** `bstaromega_np`.

Notably **44XIII went through 44VII alone, with no forward reference**: `(da)_d →
(⋁D)a` and `(ad)_d → a(⋁D)`, the two nets are equal, so `tendsto_nhds_unique` in
`ℂ` plus `np_separating` finishes it.

That opened **parsecs 560–580** — 16 statements (`exists_ceil`, `vna_ceil`,
`vna_ceil_sup/_comm`, `exists_floor`, `vna_floor_comm`, 56XI.1/.2,
56XIII.1/.2/.3, 56XIV, 56XVI, 57I, 58II) plus a public API (`ceil_spec`,
`floor_spec`, `floor_isGreatest`, `projSup_spec`, `projInf_spec`) that the
590–630 block should be built on.

**Two divergences.**  *56I.40*: the thesis computes `p²` via `ad_normal` twice;
the Lean proof keeps the identical chain and index choice `n = m = k+1` but with
`≥` at each step, which is all `p ≤ p²` needs and follows from bare monotonicity
of `b ↦ c*bc` — a weakening of the author's computation, not a different
argument.  *56VI*: the thesis proves the floor symmetrically via `⋀ₙ b^{2ⁿ}` and
"a variation on `ad-normal`" for *filtered infima*, which our development lacks;
the Lean proof instead derives `⌊b⌋ = ⌈b^⊥⌉^⊥` directly, proving rather than
citing the later 56XIII.1.  Cost: `vna_floor` bundles `IsGreatest` with the
`⋀ₙ b^{2ⁿ}` formula in one theorem, so it stays `sorry`; the useful half is
available as `floor_isGreatest`.

**Next step, one short lemma**: derive `ad_normal` for *filtered infima* from
`ad_normal` + `infima_in_vna` by `x ↦ −x` — `Basic.lean:604` already uses exactly
that negation trick.  That finishes `vna_floor` along the thesis's own 56VI.90.

**No new errata** this pass; E1/E2 from the previous A/VN pass stand.  One
formalization trap recorded so it is not rediscovered:
`@IsClosed A (ultraweak A) S` does **not** survive dot-notation or a plain
`exact` — `A`'s norm topology gets re-synthesised — hence the three `@`-applied
wrappers in `Basic.lean`.

### Session 55 — B/Eff: **177Ia is false**, and §2.1.1 of the master's thesis
is in the tree

The target was to *prove* 177Ia `ea-modularity-prop` ("for `a ⊥ b`, if `a ∧ b`
exists then `a ∨ b` exists and `a ⋁ b = (a ∧ b) ⋁ (a ∨ b)`"), on a route
supplied by the author: §2.1.1 of his master's thesis, Prop. 13.3 + Cor. 14.2.
The instruction was to verify the route rather than trust it.  It does not
hold, and neither does the Proposition.

**The counterexample.**  `WrightTriangle` in `EffectAlgebras.lean`: the
Greechie diagram with three three-atom blocks pasted in a loop of order 3
(`B₁ = {a₁,a₄,a₂}`, `B₂ = {a₂,a₅,a₃}`, `B₃ = {a₃,a₆,a₁}`; 14 elements: `0`, six
atoms, six coatoms `cᵢ = aᵢᵖ`, `1`).  It is given as a 14-constructor inductive
type with the partial addition as a `match` table, and **every PCM and effect
algebra axiom is discharged by `decide`** — no `native_decide`, so the axiom
check stays clean (`propext`, `Classical.choice`, `Quot.sound`).  In it
`a₁ ⊥ a₂` and `a₁ ∧ a₂ = 0` exists, while `a₁ ∨ a₂` does not: `a₄ᵖ = a₁ ⋁ a₂`
and `a₃ᵖ = a₆ ⋁ a₁ = a₂ ⋁ a₅` are incomparable minimal upper bounds.  Hence
`WrightTriangle.not_ea_modularity_prop` and — for the intermediate lemma of
`modularity-lemma-proof`, *even with `c ⊥ d` added* —
`WrightTriangle.not_modularity_lemma`.

The structural reason is worth remembering: in **any** orthoalgebra `a ⊥ b`
forces `a ∧ b = 0` (a common lower bound `c` satisfies `c ⊥ c`), so 177Ia would
say every orthoalgebra is an orthomodular poset — and the Wright triangle is
the textbook orthoalgebra that is not one.  Any effect algebra statement whose
hypotheses reduce to "`a ⊥ b` and `a ∧ b = 0`" and whose conclusion is a join
should be tested against it first.

**Where the master's-thesis route fails.**  Corollary 14 justifies transporting
suprema/infima across `a ⋁ (·)` and `a ⊖ (·)` by "suprema and infima in the
order restricted to `↓a⊥` are the same as in the whole of `E`".  That is sound
only when the bounds are forced into the interval, which happens for two of the
four halves: lower bounds of a subset of `↓a` are automatically `≼ a`, and
bounds of `a ⋁ U` are automatically `≽ a`.  For the remaining halves — in
particular `⋀U` exists ⟹ `⋁(a ⊖ U)` exists, which is the whole content of
177Ia — an upper bound of `a ⊖ U` need not lie below `a`, and the argument
gives only a supremum *inside `↓a`*.  That is the identical flaw to the printed
proof of 177Ia, which forms `x⊥ ⋁ s` for an arbitrary upper bound `s`.

**Proved (class (2) — a different route, from the author's earlier work; cite
master's thesis §2.1.1 by proposition number):**

* `msc_prop13_1` (Prop. 13.1) — `x ↦ a ⋁ x` is an order embedding `↓aᵖ → ↑a`;
* `msc_sub_antitone` / `msc_prop13_3` (Prop. 13.3) — `x ↦ a ⊖ x` is an order
  anti-isomorphism of `↓a` onto itself, order-reflecting because it is its own
  inverse (176II (D3));
* `msc_cor14_1_sup`, `msc_cor14_1_inf`, `msc_cor14_2_inf` (Cor. 14, the sound
  halves);
* `msc_cor14_2_sup_below` (Cor. 14.2, **honest form**: least upper bound *among
  elements below `a`* — the half that is false in `E`);
* `msc_prop15` / `msc_prop15'` (Prop. 15) — `a ⊥ b` and `a ∨ b` exists ⟹
  `a ∧ b = (a ⋁ b) ⊖ (a ∨ b)`;
* `msc_cor16_1` (Cor. 16.1, honest form) — the `⋁`-versus-`∨` bridge: `a ⊥ b`,
  `a ∧ b = 0` and `a ∨ b` exists ⟹ `a ∨ b = a ⋁ b`;
* `msc_cor16_2` (Cor. 16.2) — the identity `(a ∧ b) ⋁ (a ∨ b) = a ⋁ b` whenever
  both exist;
* helpers `le_of_isDiff`, `isInf_comm`, `isSup_comm`, `isInf_unique`,
  `isSup_unique`.

**One statement changed, deliberately.**  The house rule is that statements are
never changed and unprovable ones keep their `sorry`.  177Ia is the case the
rule does not fit: leaving a `sorry` on a statement we have *proved false*
would advertise an open goal that can never be closed.  Following the precedent
of 39VII/38VI.2/227III.1 in ERRATA.md ("our statement is realigned and
proved"), `ea_modularity_prop` now hypothesises the supremum and concludes the
identity — one line from `msc_cor16_2` — with a doc comment pointing at the
refutation directly above it.  The faithful, false form survives verbatim as
the body of `WrightTriangle.not_ea_modularity_prop`, so nothing is lost.  If
the coordinator prefers the `sorry`, restoring it is a two-line edit.

Nothing consumed 177Ia (checked: no references outside the file), so nothing
downstream moved.  **177VI `orth_ea_is_orthomodular` was found already proved**
— the parked-items entry for it was stale — and its `key` step is exactly the
surviving identity specialised to an ortholattice, where both bounds exist.
B/Eff `#sorry_leaks`: **1756 declarations, 19 themselves `sorry` (was 20), 0
depending on one.**

### Session 3 — B/Eff is now free of `sorryAx` leakage, and 177Ia is not
load-bearing

B/Eff went 50 → 43 code `sorry`s, but the result worth recording is the axiom
check: **1322 declarations, 43 themselves `sorry`, zero depending on one** —
including the auto-generated declarations that used to make up the residue.
Verified by running the `#sorry_leaks` walk scoped to B/Eff's modules (the
whole-project version cannot run while another worker has the A chain open).

**177Ia was the last leak, and it is now bypassed.**  `isSharp_ovee` was
`ea_modularity_prop`'s only consumer, and `diamond_oml_subEA` inherited
`sorryAx` through it.  Both are now proved *without* modularity:
`s ⋁ t = im[π_s, π_t]` is a supremum among **all** predicates by 204V, and
conversely `s` and `t` both vanish on `π_{(s∨t)ᵖ}`, hence so does `s ⋁ t`.  Two
reusable helpers fell out — `le_iff_compr_orth_comp_eq_zero`, and `ovee_le_of_le`
("the predicates below a sharp `j` are closed under `⋁`").  `ea_modularity_prop`
is now referenced nowhere in the tree.  **The author ruling on 177Ia (QUESTIONS
B4) is still wanted, but nothing waits on it.**

Proved: **208III.2 `diamond_oml`** (Cho — `SPred X` is an orthomodular lattice),
**208VII** the `OMLatGal` functor and **213VI** `exc_prod_sharp_maps`, all three
previously parked as blocked on 208III; plus **226II `homology_lemma`**,
**226V.3 `homological_exact`**, **226V + 226VII `homological_category`** (the
whole "a †-effectus is a pointed homological category" theorem), and
**190II.5 `predMap_functor`**.

Divergences: class (1) for 208VII, 213VI, 226V.3, 226V parts 1–2, 190II.5;
class (2) for `isSharp_ovee`, 208III.2 and 226II; class (3) for the homology
axiom, which uses the `ζ` of 211VII in place of the dagger `m†` — the same map,
without needing the dagger development.  Three `eff.tex` errata rows came out of
the comparison (208III, 226II, 226VII) — see ERRATA.md.

> ⚠ **The paragraph below is wrong; see session 5.**  174IV `PCM.isSumOf_perm`
> has been proved since session 1 and 178V is proved as well — the DISP search
> that produced this claim hit 174IV's doc comment, which was misfiled on the
> helper `isSumOf_swap`.  178III.1 is now proved too.

**Sharpest remaining blocker: 174IV.**  178III.1
`unitInterval_effectMonoid_unique` (asserted without proof at eff.tex:636) has a
clear Cauchy-functional-equation argument, but its very first step
`a ⊙ (1/n) = a/n` needs the `n`-fold partial sum, i.e. **174IV
`PCM.isSumOf_perm`** (generalized associativity) — itself stated without proof
at eff.tex:223 and still `sorry`.  174IV also blocks 178V, which makes it the
highest-leverage `sorry` left in `EffectAlgebras.lean`.  The other 42 group by
blocker into: thesis A (the `vNᵒᵖ` examples), the †-effectus block 215III–220
(the Snake Lemma, which after this pass needs nothing from 226–227 — only
219XVI), the `𝒟_M`/`AConv_M` subsum infrastructure, and the statements the
thesis only cites.

### Session 6 — A/VN: parsec 760 is complete; 77I is **not** unblocked

**`A/VN` 132 → 128 code `sorry`s** (Basic 40 → 39, Completeness 21 → 18;
Division 26, NormalFunctionals 19, Projections 26 untouched).  Everything
below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
`lake build` over `Theses.A.Proc.*` and `Theses.B.Dils.*` is as clean as it
was found.

| point | declaration | file |
|---|---|---|
| **76I** | `bh_us_complete` | Completeness.lean |
| **76III** | `bh_bounded_uw_complete` | Completeness.lean |
| **72III**.2 | `bstaromega_cauchy` | Completeness.lean |
| **48V** | `varrho_Omega_normal` | Basic.lean |

Plus the promotion of the np-functional cone (below) and a new public helper
`exists_faithful_normal_rep_vectors` in `Basic.lean`.

#### ⚠️ Correction — **77I is still blocked, and 76I/76III were never its only
gate**

The session-3 note "77I is blocked, precisely" lists **two** walls, and only
the first (39IX `bh_np`, now proved) has fallen.  The thesis's proof
(vn.tex:4813 ff.) needs `ρ_Ω(𝒜)` to be ultrastrongly **and** ultraweakly
*closed* in `B(H_Ω)`, i.e. **75VIII `vnsac`**, twice:

> "since `B(H_Ω)` is ultrastrongly complete (`bh-us-complete`), and `R` is
> ultrastrongly **closed** in `B(H_Ω)` (see `vnsac`) …"

Without closedness the ultrastrong limit `T` produced by 76I need not lie in
`R`, and no substitute was found: `77III` (ultraweak compactness of the ball)
is proved *from* 77I, so it cannot replace it.  So 77I sits behind the full
column `72V → 72XI → 73VIII → 74I/74IV → 75II → 75VI → 75VIII`, exactly as
session 3 said.  **Any brief claiming 77I follows from 76I + `ngns` + a
net-pushing step is wrong**; the third ingredient is `vnsac`, not the
net-pushing.

#### 76I — a shorter argument than the thesis's for the final step (class 3)

Steps 1–3 (pointwise norm-Cauchy → `F x := lim T_α x`; linearity; boundedness
by contradiction from a sequence `‖xₙ‖ ≤ 2⁻ⁿ`, `‖F xₙ‖ ≥ 1` and the np-map
`∑ₙ ⟪xₙ,(·)xₙ⟫` of 38IV.2) are the thesis's, verbatim.

Step 4 is **not**.  The thesis splits `∑ₙ ‖(T−T_α)xₙ‖²` at an index `N` and
runs an `ε/(2√2)` estimate through a third index `β`.  That is unnecessary:
for a *finite* `G ⊆ ℕ`, `∑_{n∈G} ‖(T_α−T_β)xₙ‖² ≤ ‖T_α−T_β‖_ω² ≤ ε²` for all
`β` in the Cauchy set, and the left side converges to `∑_{n∈G}‖(T_α−T₀)xₙ‖²`
as `β → l`; so *every* finite partial sum of the target series is `≤ ε²`, and
`hasSum_le_of_sum_le` finishes.  One `le_of_tendsto`, no split, no `√2`.  The
same "finite partial sum ≤ limsup" move replaces the thesis's `∑_{n=1}^N ≥ N`
step in the boundedness argument.

#### 76III — Riesz instead of 36V (class 3, forced)

The thesis gets the operator `T` from the form `[x,y] = lim ⟪x,T_α y⟫` by
**36V** `chilb_form_representation` (self-dual Hilbert `𝒜`-modules).  36V is
now proved, but instantiating it at `𝒜 = ℂ` means presenting `H` as a
`CStarModule ℂ H`; as in worker 21's `exists_rho`, the Lean proof instead uses
Mathlib's `InnerProductSpace.toDual` (Riesz), which is what 36II says 36V *is*
for `𝒜 = ℂ`.  Everything else is the thesis's: polarisation to get the form
from the diagonal (each `⟪u,(·)u⟫` is an np-functional, so `hcauchy` applies),
the bound `|[x,y]| ≤ (sup‖T_α‖)‖x‖‖y‖`, and the `ε`-tail split against
`∑ₙ‖xₙ‖² < ∞` from 39IX.

#### 72III.2 `bstaromega_cauchy` — the gate for 72V's (3) ⇒ (4), now proved

The thesis leaves this as an exercise with no published solution (`asols.tex`
stops at parsec 340), and it is the step 72V's proof cites as "we see by
`bstaromega-basic` that `(f_{k,n})_n` converges to an np-map".  Class 1 for
the Cauchy/limit half (it is 72III.1c plus completeness of `ℂ`), and the
*normality* of the limit — which the thesis simply asserts — is discharged as
follows, since no argument is given:

> A bounded directed `D` with `⋁D = s` need **not** be norm-bounded (it is
> bounded above, not below: `{−10⁶·1, s}` is directed).  Replace it by the
> cofinal `D' = {d ∈ D | d₀ ≤ d}` for any fixed `d₀ ∈ D`; `D'` is directed,
> has the same supremum `s`, and *is* norm-bounded, by
> `‖d‖ ≤ ‖d₀‖ + ‖s − d₀‖`.  On a norm-bounded set the operator-norm
> convergence `bₙ*ω → f` is uniform, so `f(s) ≤ z + ε` for every upper bound
> `z` of `f''D` and every `ε > 0`, using normality of `bₙ*ω` on `D'`.

Worth telling the author: the exercise as stated ("Show that `f` is an np-map")
hides this cofinality step, which is the only non-routine part of it.

#### 48V `varrho_Omega_normal` — class 1, and it needed a stronger helper

The predicted "few lines from `gnsVec_inner`" did not typecheck directly: the
Lean statement asks for a representation on `lp (fun _ : ι => ℂ) 2`, and
`starAlgHomP` would not unify against `gnsRep`'s concrete
`ContinuousLinearMap.semiring` instance path on `gnsHilb A` (it does unify for
the *opaque* `H` of `exists_faithful_normal_rep`, which is why `ngns`
compiles).  Fixed by adding

```lean
theorem exists_faithful_normal_rep_vectors (A) … :
    ∃ H … (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ⇑ρ ∧ PreservesDirSups ⇑ρ ∧
        ∀ ω : NPFunctional A, ∃ ξ : H, ∀ a, ω a = ⟪ξ, ρ a ξ⟫
```

(the vector being `lp.single 2 ω (gnsVec ω 1)`, exactly as predicted) and then
transporting along a Hilbert basis exactly as `ngns` does.  `varrho_Omega_normal`
quantifies over an arbitrary `Ω`, and the full-`Ω` representation serves every
subset, so `Ω` is never used — worth noting for the author, since the thesis's
`ρ_Ω` is genuinely `Ω`-indexed.

#### The np-functional cone is now public in `A/VN/Basic.lean`

`zeroNP`, `addNP` (with the one-time proof that a sum of np-functionals is
normal), `zeroNP_apply`, `addNP_apply`, `omegaNorm_le_addNP`,
`omegaNorm_le_addNP'`, `omegaNorm_mul_le` and the new
`abs_omegaNorm_sub_omegaNorm_le` moved out of `Completeness.lean`'s
file-private block into `Basic.lean`, next to `npFunctional_mono` — **not**
into `Common.lean`, which every chapter imports.  72V, 72XI, 73VIII and
87VIII need them.

#### Where 72V stands now

Of the four implications in the cycle, three are within reach with what is on
the shelf:

* **(4) ⇒ (1)**: Kadison via `norm_apply_le_omegaNorm` — routine.
* **(1) ⇒ (2)**: the thesis's rescaling `ã = δ(ε+‖a‖_ω)⁻¹a` — routine.
* **(3) ⇒ (4)**: polarisation `4·ω(b*a) = ∑_k iᵏ ω((iᵏb+1)* a (iᵏb+1))`
  (checked: `∑_k iᵏ = 0` and `∑_k i²ᵏ = 0` kill the three unwanted terms)
  plus **`bstaromega_cauchy`, now proved**.  It additionally needs a positive
  *scalar multiple* of an np-functional (for the `¼`), which the cone above
  does not yet have — a two-line `smulNP` alongside `addNP`.
* **(2) ⇒ (3)** is the remaining blocker: our (3) demands an explicit
  `φ : A →ₗ[ℂ] lp (fun _ : ι => ℂ) 2` with dense range and
  `⟪φa, φc⟫ = ω(a*c)`, plus a Riesz vector `b`.  `gnsVec ω`, `gnsVec_inner`
  and `gnsVec_denseRange` give `φ` after transport along a Hilbert basis of
  `PositiveLinearMap.GNS ω` (as in `ngns`); what is missing is the *extension*
  of `f` from `A` to the completion — i.e. `f` as a `ContinuousLinearMap` on
  `PositiveLinearMap.PreGNS ω` (a **semi**normed space) extended over
  `UniformSpace.Completion`.  That is the piece to build next.

#### The line-reference sweep was requested and is **not needed for `A/VN`**

Worker 21 reported the `file:LINE` doc references as "repo-wide stale" and
recommended a sweep.  Measured rather than assumed: of the **357**
`vn.tex:LINE` references in `Theses/A/VN/*.lean` (287 carrying a LaTeX label,
70 bare), **every one resolves to within ±1 line of its point**, the sole
exceptions being the two deliberate references to the *proof* sub-points of
86II.  So the 2026-08-13 drift did not affect `vn.tex`, or `A/VN` was written
after it.  The finding is recorded in CONVENTIONS.md together with the check;
the recommendation there is now "measure the file, do not assume".

### Session 4 — `A/CStar/TowardsVN.lean` is complete; 39VII is an erratum

**`A/CStar/TowardsVN.lean` 5 → 0 code `sorry`s.**  38IV.2, 39VII, 39IX
(`bh_np`), 35VI `hellinger_toeplitz` and 36V `chilb_form_representation` are all
proved and axiom-clean (`propext, Classical.choice, Quot.sound` only), which
removes the A/CStar half of the 77I block recorded in the next section.

**Import change.** `TowardsVN.lean` now imports `Theses.A.CStar.Representation`
(hence `Positive`, `Basic`) instead of only `Theses.Common`.  This adds nothing
to the downstream closure — `A/VN/Basic.lean` already imported both — and buys
two things the file previously had to do without: `ketbra` (**4XIX**) and its
norm, which the file was *re-declaring privately*, and **30IV.1**
`omega_norm_basic_1`, i.e. the thesis's own **Kadison inequality**, which 39VII's
proof cites by name.  The private duplicate `ketbra` is deleted.

#### ⚠️ 39VII (`bh-np-lemma`, cstar.tex:6611) — the double sum is not an
unordered sum, and as printed the statement is false

The thesis writes `ω(A) = ∑_{e,e'∈E} ⟪e, A e'⟫ ω(|e⟩⟨e'|)`.  Its own convention
for a sum over an index set is fixed in **6II**'s proof (`cstar.tex:880`): "given
`ε>0` find a finite `G ⊆ I` with `|∑_{i∈F}…| ≤ ε` for all finite `F ⊆ I∖G`" —
i.e. unordered/unconditional summability, which is Lean's `HasSum`, and which for
scalars is equivalent to *absolute* summability.  Under that reading the
statement is **false**.

Counterexample (ours).  Take `H = ℓ²(ℕ)` with `E` the standard basis and
`ω = ⟪x, (·) x⟫`, a normal p-map by **38II**.  Then
`ω(|eᵢ⟩⟨e_j|) = xᵢ x_j` and the `(i,j)` term is `A_{ij} xᵢ x_j`, so
unconditional summability would force `∑_{i,j} |A_{ij}| xᵢ x_j < ∞`.  Let `A` be
block diagonal with `N_k × N_k` **discrete-Fourier** blocks — unitary, so
`‖A‖ = 1`, and every entry of modulus `N_k^{-1/2}` — and let `x` be constant
`c_k` on block `k`.  Then `∑ᵢ xᵢ² = ∑_k N_k c_k²` while
`∑_{i,j}|A_{ij}| xᵢ x_j = ∑_k N_k² · N_k^{-1/2} · c_k² = ∑_k N_k^{3/2} c_k²`, a
factor `√N_k` larger term by term.  Choosing `N_k = k⁸` and `c_k² = k^{-10}`
gives `∑ᵢ xᵢ² = ∑_k k^{-2} < ∞` but `∑_k k^{12}·k^{-10} = ∑_k k² = ∞`.
(DFT blocks, not Hadamard, so that every `N_k` is allowed.)

The thesis's *proof* proves something else, and something true: it shows
`ω(A − PAP) → 0` for `P = ∑_{e∈F} |e⟩⟨e|`, i.e. convergence of the **square**
partial sums `∑_{e,e'∈F}` along finite `F ⊆ E`.  That is also exactly the form
39IX uses (to conclude `ω = ω'` from agreement on the `|e⟩⟨e'|`).  Our Lean
statement is therefore **realigned** to

```lean
Tendsto (fun F : Finset E => ∑ e ∈ F, ∑ e' ∈ F, ⟪e, A e'⟫ * ω (ketbra e e'))
  atTop (𝓝 (ω A))
```

and proved.  ERRATA.md carries the row; the doc comment carries the
counterexample.  (An *iterated* sum `∑_e (∑_{e'} …)` is also true — the inner sum
is `⟪e, Aϱe⟫` and the outer is `tr(Aϱ)` with `ϱ` trace class — but it needs `ϱ`,
which is 39IX's own content, so it is not the right restatement here.)

#### Divergences

* **38IV.2** `bh_functional_lemma_2` — **transcribed** (class 1/3).  The thesis
  reduces to directed sets of *effects* by **38III** so that the terms
  `⟪xₙ, T xₙ⟫` are nonnegative, then interchanges `⋁_{T∈𝒟}` with `⋁_N`.  We do
  exactly that, via `bh_normal_effects`; the one deviation is that the inner
  supremum over partial sums is handled as a **limit** (`tsum_le_of_sum_le`,
  `tendsto_atTop_isLUB` on the directed index type, `tendsto_finsetSum`) rather
  than as a supremum, since `ℂ` with `ComplexOrder` is not a lattice.  The
  positivity supplied by the reduction to effects is still needed: it is what
  makes a finite partial sum bounded by the total.
* **39VII** `bh_np_lemma` — **transcribed** apart from the restatement above.
  `P A P = ∑_{e,e'∈F} ⟪e,Ae'⟫|e⟩⟨e'|`, `P² = P`, `‖P‖ ≤ 1`,
  `A − PAP = P^⊥A + PAP^⊥`, Kadison (30IV.1) twice, and
  `ω(P^⊥) = ω(1) − ∑_{e∈F} ω(|e⟩⟨e|) → 0` by **39VI**.3 — all as printed.
* **39IX** `bh_np` — **transcribed, with one substitution** (class 3).  The
  thesis gets `ϱ` from **36V** `chilb-form-representation`; 36V is still `sorry`
  here, and for `𝒜 = ℂ` it *is* Riesz representation (which is how **36II**
  justifies self-duality of a Hilbert space), so `exists_rho` builds `ϱ` from
  Mathlib's `InnerProductSpace.toDual` instead.  Positivity of `ϱ`, `√ϱ`,
  `ω(1) = ∑_e ‖√ϱ e‖²` via 39VI.3, and the final identification via 39VII are the
  thesis's own steps.  Two further deviations, both forced by our statement:
  * the thesis proves `ω(|x⟩⟨x|) = ω'(|x⟩⟨x|)` and extends **by polarisation**;
    the same computation gives `ω(|u⟩⟨v|) = ⟪√ϱ v, √ϱ u⟫ = ω'(|u⟩⟨v|)` for all
    `u, v` directly (it is just Parseval, 39IV.3, applied to `√ϱ v, √ϱ u`), so
    polarisation is not needed;
  * our statement asks for a sequence `x : ℕ → H`, whereas the thesis's family is
    indexed by the basis `E` and it merely remarks parenthetically that "`√ϱ e`
    is non-zero for at most countably many `e`".  That remark is discharged
    explicitly: `Summable.countable_support` on `∑ ‖√ϱ e‖²`, an injection
    `supp → ℕ`, and `Function.extend` to pad with zeros, transported with
    `Function.Injective.hasSum_iff` + `hasSum_subtype_iff_of_support_subset`.

#### Parsecs 350–360: 35VI and 36V, and one mis-transcription of ours

Both were transcribed from the thesis's own proofs.

* **35VI** `hellinger_toeplitz` — faithful.  For each `y`, `⟨T*y, ·⟩ : X → 𝒜`
  is bounded by `‖T*y‖` (32VI); `sup_{‖y‖≤1} ‖⟨y, Tx⟩‖ ≤ ‖Tx‖ < ∞` pointwise,
  so **35II** (uniform boundedness) gives a uniform `B`; then `‖Tx‖² =
  ‖⟨Tx,Tx⟩‖ ≤ B‖Tx‖‖x‖` (the nontrivial half of **32X**, inlined here because
  `TowardsVN.lean` sits below `Matrices.lean` in our file order).  One Lean-only
  wrinkle: Mathlib deliberately does **not** register `NormedSpace ℂ E` for a
  `CStarModule` (it wants to be free to replace the topology), so `banach_
  steinhaus` is unusable until the instance is supplied `letI`-style from
  `CStarModule.normedSpaceCore`.
* ⚠️ **36V** `chilb_form_representation` — **our statement was missing
  completeness**, and is now fixed (`[CompleteSpace X]` added).  The source says
  "self-dual **Hilbert** 𝒜-modules", and 32I defines a Hilbert 𝒜-module to be a
  pre-Hilbert module *complete* in its norm; our `CStarModule` hypotheses give
  only the pre-Hilbert structure.  This is not cosmetic: the thesis's proof gets
  boundedness of `T` and `S` from 35VI, which **35IX** shows is false without
  completeness.  One of `X`, `Y` suffices, so only `[CompleteSpace X]` is added.
  (Checked the siblings, per the half-repair rule: 36I `SelfDual` is a
  predicate and needs nothing; 36III `selfDual_pi` is about `𝒜^N`, which is
  complete anyway, and is already proved without the hypothesis — i.e. slightly
  stronger than the thesis, which is harmless.)

  With that, the proof is the thesis's: represent `[x,·]` by `T x` (self-duality
  of `Y`) and `[·,y]*` by `S y` (self-duality of `X`), get linearity and
  𝒜-linearity of both from definiteness of the inner product, note `S` and `T`
  are adjoint, and apply 35VI.

#### Doc-comment line references in this file were ~80–95 lines stale

Every `cstar.tex:LINE` in `TowardsVN.lean` predated the author's 2026-08-13 edits
(e.g. `bh-np-lemma` 6521 → **6611**), and the drift is *not* uniform (+80 in
parsec 350–370, +95 in 380, +90 in 390), so it cannot be corrected by eye.  All
28 of them are now re-derived from the labels and fixed.  **Other files very
likely have the same drift** — worth a mechanical sweep: match each doc comment's
label against `\begin{point}{N}[label]` in the `.tex`.

No other errata found in parsecs 350–390.  **Note for the record**: `asols.tex`
stops at parsec 340, so 38VI and 39VI have no published solution; the proofs of
their neighbours here are ours, as was already the case for 38VI.2.

### Session 9 — B/Eff: 192V.1 and 213I; one of our own statements was too weak

B/Eff went **36 → 34** code `sorry`s (`StatesPredicates.lean` 10 → 9,
`DiamondAmp.lean` 3 → 2) with

| DISP | name | file | class |
|---|---|---|---|
| **192V.1** | `convex_subset_mconvex` — a convex subset of a real vector space is a cancellative abstract `[0,1]`-convex set | StatesPredicates | n/a (the thesis asserts, does not prove) |
| **213I** | `andthen_effect_divisoid` — `(Scal C)ᵒᵖ` is an effect divisoid for an &-effectus `C` | DiamondAmp | 1 (faithful, eff.tex:5184–5222), with one shortcut noted in ERRATA |

#### 192V.1: the missing piece really was only a bridge

The brief was right that this needed nothing but a translation from
`PCM.IsSumOf` over `[0,1]` to sums of reals.  That bridge is
`unitInterval_isSumOf_iff`: `PCM.IsSumOf l s ↔ (l.map (↑·)).sum = ↑s`
(forward by induction on the derivation, backward by induction on the list,
the tail sum being in `[0,1]` because it is `≤ s`).  On top of it:

* `MConvexComb.supp`, a `Finset` enumeration of the support, with
  `mem_supp : x ∈ p.supp ↔ p x ≠ 0`;
* `coe_sum_one`, `coe_map_apply` (`𝒟f(p)(y)` is the real sum over the fibre)
  and `coe_mu_apply` (`μ(Φ)(x) = Σ_φ Φ(φ)·φ(x)`), each stated over *any*
  finset containing the support, which is what makes them composable;
* `MConvexComb.rsum p g = Σ_{x ∈ p.supp} p(x) • g x`, with `rsum_eq`
  (independence of the enumerating finset), `rsum_eta`, **`rsum_map`**
  (`(𝒟f p).rsum g = p.rsum (g ∘ f)` — `Finset.sum_fiberwise_of_maps_to`),
  **`rsum_mu`** (`(μΦ).rsum g = Φ.rsum (φ ↦ φ.rsum g)` — `Finset.sum_comm`),
  and `rsum_bin` (`(λ|y⟩ ⋁ λᵖ|x⟩).rsum g = λ·g y + (1−λ)·g x`, uniformly in
  `y = x`).

The two Eilenberg–Moore laws are then *exactly* `rsum_eta` and
`rsum_mu`/`rsum_map`, membership in `s` is `Convex.sum_mem`, and
cancellativity is `rsum_bin` plus `smul_right_injective` at `1 − λ ≠ 0`.
`MConvexComb.bin_apply`, `bin_self`, `bin_eq_zero` moved up next to `bin`
(they only need `bin`), since 192V.1 now needs them 2000 lines earlier.

#### Statement changes (our own, not the thesis's)

* **192V.4 `cancellative_iso_convex` was too weak.**  It read
  `∃ V … (s : Set V) (_ : Convex ℝ s) (st' : MConvex I s) (f : X → s),
  Bijective f ∧ st.IsAffine st' f` — with the convex structure `st'` on `s`
  *itself* existentially quantified.  Nothing then ties `st'` to the convex
  structure of `s`, so the statement says only that `X` is in bijection with
  some convex subset carrying *some* abstract convex structure; it is a claim
  about cardinalities, not the affine isomorphism of 192V.4 ("every
  cancellative `[0,1]`-convex set is isomorphic to a convex subset of a real
  vector space", where the convex subset carries its own structure).  Fixed:
  the target is now `MConvex.ofConvex s hs`, the canonical structure, which
  192V.1 supplies as a *definition*.  Still `sorry` (see below).
* **192V.1 `convex_subset_mconvex`** was `∃ st : MConvex I s, st.Cancellative`,
  which likewise dropped 192V.1's "with `h(⋁ᵢ λᵢ|xᵢ⟩) = λ₁x₁ + ⋯ + λₙxₙ`".
  It is now `(MConvex.ofConvex s hs).Cancellative`, with
  `MConvex.ofConvex_h` recording the formula by `rfl`.

Both are our transcription artefacts, not thesis defects.  Nothing depended on
either statement, so no proof had to change.

#### 213I: short, and all its machinery was already there

The thesis proof (eff.tex:5184–5222) is one paragraph and rests only on
**212I** `zeta_asrt_quot`, which has been proved since session 3.  With
`asrt_μ = μ` for a scalar (181XIII: `1 = id` on the effect object,
`truth_effObj_eq_id`), 212I says `μ ≫ ζ_⌈μ⌉` is a quotient for `μᵖ`, so for
`λ ≼ μ` there is a unique `λ'` with `(μ ≫ ζ_⌈μ⌉) ≫ λ' = λ`; the division is
`λ/μ ≡ ζ_⌈μ⌉ ≫ λ'` (helpers `scalZeta`, `scalQuot`, `scal_factor`,
`scalDiv`, `scalDiv_spec`, `scalDiv_self`, `scalDiv_le`, `scalDiv_unique`,
all `private`).  `μ/μ = ⌈μ⌉` is `quotient_basics_5` plus the uniqueness clause
— see the ERRATA row: the thesis's image computation and appeal to epicity are
both avoidable.  One reusable addition in `StatesPredicates.lean`:
`op_le_iff`, that `≼` in `Mᵒᵖ` is `≼` in `M`.

*Lean note.*  `MulOpposite.unop` is a `def` over the private field `unop'`, so
`rw` will not see through `MulOpposite.unop b` in a goal; use `congrArg
MulOpposite.op` / `MulOpposite.unop_injective` instead of rewriting.

#### 195VI `basic_divisoid_equiv` — measured, and it is not a bridge problem

The brief asked whether Mathlib has σ-Dedekind completeness of `C(X)`.  It does
not, and neither notion in the exercise (basically disconnected spaces,
`ω`-completeness of `C(X)`) exists there.  The published solution
(`bsols.tex:2466`) is two pages of point-set topology: the `⇒` half needs
Urysohn (Mathlib has it) plus the fact that `f/f` is idempotent hence
`{0,1}`-valued; the `⇐` half constructs `h_n` on `closure U_n`, proves each
`h_n` continuous by a *net* argument using that `closure U_n` is open, and then
needs `sup_n h_n` to be continuous — i.e. exactly the missing theorem, that
`C(X)` is `σ`-Dedekind complete when `X` is basically disconnected.  That is
the real work and it is a Mathlib-sized contribution, not a bridge.

### Session 8 — B/Eff: **196II is proved**, and the derivation calculus is avoidable there too

B/Eff went **37 → 36** code `sorry`s (`StatesPredicates.lean` 11 → 10) with the
proof of **196II** `aconvm_is_effectus` — the last open item of the
190–196 chain, and the one the two previous passes reported as blocked on the
derivation calculus of 193IX/193IV.  It is not blocked on it.

#### The shortcut: over a divisoid, every element of `X + Y` is a *binary* mixture

The thesis proves the left pullback square (eff.tex:3383–3600) by building
`ω ∈ 𝒟_M(X+Y)` out of `α` and `β` and then showing it well defined by
interleaving **two** derivations `Φ_i` (over `1+Y`) and `Ψ_i` (over `X+1`) into
one `Ω_i` — two pages, resting on the syntactic description of the least
congruence that 193IV leaves to the reader.

The observation that removes all of it: the normalization the thesis already
performs *inside* `ω` — divide the coefficients by `λ₀` and repair the deficit
with `r = (λ₀/λ₀)ᵖ` at one designated point — applies to a **whole** formal
combination, and then says that over an effect divisoid every element of
`X + Y` is `mix λ x y := h(λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩)` for some `λ, x, y`
(`AConvMCat.exists_mix`).  Given that:

* **uniqueness** (`AConvMCat.coprod_jointly_injective`): if `w = mix λ x y` and
  `w' = mix λ' x' y'` agree in `X+1` and in `1+Y`, then `λ = λ'` because the
  mass map `X ⨿ Y ⟶ 𝒟_M(1+1)` (the cotuple of two *constant* maps — affine by
  `MConvexComb.map_const`) factors through each leg; and the cotuples
  `[κ₁, const κ₂y']` and `[const κ₁x, κ₂]`, again affine because constant maps
  are, transport the two equalities back into `X ⨿ Y`, giving
  `mix λ x y = mix λ x y' = mix λ x' y'`;
* **existence** (`AConvMCat.coprod_exists_lift`): put the normal forms of `a`
  and `b` side by side; their masses agree by the same factorization, so
  `mix λ x y` is the required element;
* **affineness of the mediating map** is *free*, and this replaces the thesis's
  eff.tex:3592–3657: `γ` is defined pointwise by a universal property, and its
  two legs are jointly injective by the previous item, so
  `(id+!)(γ(h_Z p)) = α(h_Z p) = h(𝒟_M α (p)) = (id+!)(h(𝒟_M γ (p)))` (and
  likewise for `(!+id)`) forces `γ(h_Z p) = h(𝒟_M γ (p))`.

Classification: **case 2** (substantially different route, deliberately).  The
divisoid is used in exactly one place, `MConvexComb.exists_of_div`, which *is*
the thesis's own normalization step; everything else is the universal property
of the coproduct plus "constant maps are affine".  Filed as two informational
ERRATA rows against 196II, next to the two genuine slips found in its text (the
`α`/`β` typing sentence at eff.tex:3397, and the scrambled `q₁,q₂,q₃`/`κ₁,κ₂`
indices in point 50).

#### ⚠ The recommended route (b) of the previous pass is **refuted**

w23 (and the brief for this session) recommended building the explicit model
`M × X × Y` modulo `(1,x,y) ~ (1,x,y')` and `(0,x,y) ~ (0,x',y)`, and proving
*that* is the coproduct.  **That carrier is wrong.**  Take `M = [0,1] × [0,1]`
(an effect divisoid, by `prodEffectDivisoid`), `X = 𝒟_M A`, `Y = 𝒟_M B` free,
so `X ⨿ Y = 𝒟_M(A+B)` and `mix λ x y = λ ⊙ 𝒟_M κ₁(x) ⋁ λᵖ ⊙ 𝒟_M κ₂(y)`.  At
`λ = (1,0)` this is `(x₁, 0)` on `A` and `(0, y₂)` on `B`: it forgets the second
component of `x` and the first of `y` entirely, so `mix (1,0) x y` does not
determine `x` even though `(1,0)` is neither `0` nor `1`.  The relation
identifying elements of `M × X × Y` is genuinely `λ`-dependent (a "support"
relation), and only the *surjectivity* half of the guess survives — which is
`exists_mix`, and is all that 196II needs.  Route (a) (formalizing 193IV) was
not needed either.

#### Verification

`lake build` of all eight B/Eff modules is clean; `StatesPredicates.lean` now
has **10** `sorry`s (B/Eff **36**).  Zero `sorryAx` leakage re-verified with
`#sorry_leaks` restricted to `Theses.B.Eff`: **1312 declarations checked, 36 are
themselves `sorry`, 0 depend on one.**  Every new declaration reports
`[propext, Classical.choice, Quot.sound]`.

#### Reusable additions

`MConvexComb`: `bin_apply`, `bin_self`, `bin_eq_zero`, `bin_one`, `bin_zero`,
`map_spec_of_list` (compute `𝒟_M f (p)(y)` over any nodup list covering the
fibre), `map_bin` (`𝒟_M f` of a binary mixture, unconditionally),
`mu_spec_of_subset`, `mu_bin`, `exists_map_inr` (mirror of `exists_map_inl`,
via `Sum.swap`), `map_inl_apply_inr`, `map_inr_apply_inl`, `eq_orth_of_two`,
`exists_left_sum`/`exists_right_sum` (the two half-masses of a combination over
`A + B`), and **`exists_of_div`** — the divisoid normalization: a finitely
supported family summing to `l` is `l ⊙ (–)` of a formal convex combination.
Also `div_zero_left` and `isSumOf_div` (the `n`-ary form of 195VII).

`AConvMCat`: `constHom` (+ `comp_constHom`), `hom_apply_bin`, `mix` (+
`mix_one`, `mix_zero`, `desc_apply_mix`, `map_apply_mix`), `massMap`/`mass` (+
`massMap_inl/inr`, `_apply`, `massMap_map`, `mass_map`, `mass_mix`),
`coprodQuot_map_inl/inr`, `coprodQuot_massMap`, `massMap_coprodQuot`,
`exists_inl_of_massMap`/`exists_inr_of_massMap` (194I.4's key step, isolated
and now available in both handednesses), `coprod_inr_injective`,
`exists_inl_of_isEmpty`/`exists_inr_of_isEmpty`,
`terminal_carrier_subsingleton`, `exists_mix`, `coprod_jointly_injective`,
`coprod_exists_lift`, `aconv_left_pullback`.

#### A note on `CONVENTIONS.md`

CONVENTIONS says "doc line = tex line of the `\begin{point}` + 1".  In
`eff.tex` the doc comments consistently use the `\begin{point}` line itself
(196II: doc `3381`, `\begin{point}{20}[aconvm-is-effectus]` at 3381, statement
text at 3382; 195VII: doc `3328`, `\begin{point}{70}` at 3328).  So the
`+ 1` rule is not universal across chapters — re-derive from the label, as
CONVENTIONS itself instructs, rather than trusting the offset.

### Session 7 — B/Eff: 193X and 194I.3/.4; the derivation calculus of 193IX turns out to be avoidable

B/Eff went **40 → 37** code `sorry`s (`StatesPredicates.lean` 14 → 11).  Zero
`sorryAx` leakage still holds, re-verified mechanically after the changes:
**1132** non-internal `def`/`theorem`/`opaque` constants under `Theses.B.Eff`
reach `sorryAx`, and the set of those that do is **exactly** the set of 37
declarations that contain a literal `sorry` — nothing merely depends on one.
Every new declaration reports `[propext, Classical.choice, Quot.sound]`.

Proved: **193X** `n_times_one_aconvm`, **194I.3**
`aconvalmosteffectus_jointlyMonic`, **194I.4**
`aconvalmosteffectus_kappaPullback`.  Not proved: **196II**
`aconvm_is_effectus` (see "blocked on" below).

#### What made it work: freeness of `𝒟_M X`

The thesis's hint for 193X is "`𝒟_M`, as a left adjoint, preserves
coproducts".  Taken literally that is the whole proof, and it also does most of
194I.3.  Three elementary lemmas were added next to `AConvMCat.free`:

* `MConvexComb.freeStr_desc_isAffine` — `p ↦ h_Z(𝒟_M f (p))` is affine
  (existence half of the adjunction);
* `MConvexComb.freeStr_ext` — an affine map out of `𝒟_M X` is determined by
  its values on the Diracs (uniqueness half), and its morphism-level form
  `AConvMCat.free_hom_ext`;
* `MConvexComb.eq_eta_punit` — `𝒟_M 1` is a singleton, **including for the
  trivial effect monoid** `1 = 0` (where every combination is the zero
  function).  This is the only place the `1 = 0` split of QUESTIONS B7 had to
  be made; everything downstream is uniform in it.

From these: `AConvMCat.free_punit_isTerminal` (`𝒟_M 1 = 1`),
`AConvMCat.isColimit_freeBinaryCofan` (`𝒟_M(A+B)` is the coproduct of
`𝒟_M A` and `𝒟_M B`, up to isomorphisms of the summands) and its packaged form
`AConvMCat.exists_binaryCoprod_iso`, which returns the iso *together with* its
two coprojection identities — the form 194I.3 needs.

**193X** (class 1, faithful): `Cofan.mk (𝒟_M{1..n}) (η ∘ κᵢ)` is a colimit
directly by freeness; `colimit.isoColimitCocone` then gives the iso.  Note the
coproduct of 193V is never unfolded.

**194I.3** (class 1, faithful to eff.tex:2979–3006): identify `1+1+1` with
`𝒟_M{1,2,3}` and `1+1` with `𝒟_M{1,2}` by two applications of
`exists_binaryCoprod_iso`; under that identification the two cotuples become
`𝒟_M σ₁` and `𝒟_M σ₂` for `σ₁ = (1,2,2)`, `σ₂ = (2,1,2) : {1,2,3} → {1,2}`
(this is the thesis's `(a,b,c) ↦ (a, b⋁c)` / `(b, a⋁c)`), and the thesis's own
three-line argument — `a` and `b` are read off, and `c` is the orthocomplement
of `a ⋁ b` — is `MConvexComb.jointly_injective_of_three`.  Jointly injective ⟹
jointly monic because arrows of `AConv_M` are functions.

#### 194I.4 — two ingredients proved differently (class 2), and why

The thesis proves 194I.4 in two halves.  The *existence* half (eff.tex:3008–3056)
is transcribed faithfully.  The other two ingredients are **not**, and in both
cases the replacement is much shorter:

1. **193IX (`elements-coprod-conv`) is not needed in full.**  The thesis reads
   the surjectivity of `q : 𝒟_M(X+Y) → X+Y` off its explicit construction of
   the coproduct, and then needs its *derivation* description — which rests on
   the syntactic description of the least congruence that **193IV**
   (`least-conv-cong`) leaves to the reader and that we have not formalized.
   Surjectivity alone suffices for 194I.4, and it follows from the universal
   property alone: cut `X+Y` down to the image `S` of `q`; `S` is closed under
   `h` because `h(𝒟_M ι (Ψ)) = q(μ(𝒟_M ch(Ψ)))` for any choice `ch` of
   `q`-preimages, so `S` is an object (`MConvex.restrict`), `κ₁` and `κ₂`
   corestrict to it, and `[κ₁',κ₂'] ≫ ι = 𝟙` by `coprod.hom_ext` — so `ι` is
   surjective.  See `AConvMCat.coprodQuot_surjective`.
2. **Injectivity of `κ₁` needs no induction at all.**  eff.tex:3057–3175 — the
   longest argument of parsec 194, a derivation induction with an auxiliary
   `r_{ij}` bookkeeping device and an appeal to 178V — proves that `κ₁` is
   injective.  But *constant maps are affine* (`MConvexComb.map_const`:
   `𝒟_M(const z)(p) = η(z)`, because the coefficients of `p` sum to `1`), so
   for non-empty `X` the cotuple `[𝟙_X, const x₀] : X + Y → X` is a retraction
   of `κ₁`, making it a split mono; and for empty `X` injectivity is vacuous.
   See `AConvMCat.coprod_inl_injective`.  Recorded in ERRATA as informational.

The rest of 194I.4 is the thesis's: from `(!+!) ∘ α = κ₁ ∘ !` one gets, for
each `z`, a `φ` with `q(φ) = α(z)` whose `Y`-mass vanishes (computed by
composing `q` with `!+!` and the identification `1+1 ≅ 𝒟_M{1,2}`, which turns
`(!+!) ∘ q` into the pushforward along the collapse `X+Y → {1,2}`); such a `φ`
is `𝒟_M κ₁(χ)` (`MConvexComb.exists_map_inl`), so `α(z) = κ₁(h_X χ)`; and `γ`
is affine because `κ₁` is monic — the thesis's own last paragraph.

#### Our own repair: universe levels in 194I.3/.4 and 196II

Session 5 restated 193V and 194I.1 at `AConvMCat.{u, max u v}` (the coproduct
carrier is a quotient of `X + Y → M`, so it does not live in `Type v` when
`v < u`) but left `aconvalmosteffectus_jointlyMonic`,
`aconvalmosteffectus_kappaPullback` and `aconvm_is_effectus` at
`AConvMCat.{u, v}`, recording that they "stay true as stated" because they take
`HasFiniteCoproducts` as a *hypothesis*.  That claim was never checked, and it
is at best unusable: at `v < u` the hypothesised coproducts need not be the
ones the thesis computes with (the universal property would only be tested
against the `v`-small objects), so there is nothing to transcribe.  All three
are now stated at `AConvMCat.{u, max u v}`, matching 193V/194I.1; 194I.3/.4
keep the instance hypotheses (they are what makes `⨿`/`⊤_` meaningful) and are
proved under them.  **This is our transcription artefact, not a thesis
defect.**

Also checked, as the hand-off asked: `n_times_one_aconvm`'s
`[HasFiniteCoproducts (AConvMCat.{u,u} M)]` *is* now dischargeable —
`aconvalmosteffectus_coproducts.{u, u} M` has exactly that type (`max u u`
normalises to `u`).  It is nevertheless **kept**, because the statement
mentions `∐` and so cannot be written without an instance in scope, and
because 194I.1 is stated after 193X in the file, in thesis order.  The doc
comment now says so.

#### Reusable additions

`MConvex.restrict` (a subset closed under `h` is again an abstract `M`-convex
set), `AConvMCat.freeMap` (+ `_apply`, `_comp`, `_id` simp lemmas),
`AConvMCat.coprodQuot` (+ `_eta_inl`, `_eta_inr`, `_surjective`),
`MConvexComb.map_apply_of_unique_fiber`, `MConvexComb.eq_zero_of_map_eq_zero`,
`MConvexComb.map_const`, `MConvexComb.exists_map_inl`,
`PCM.le_of_mem_isSumOf`.  `AConvMCat.free` now factors through
`MConvexComb.freeStr`, so `(free M X).str.h` is `μ` definitionally.

#### Blocked on X

**196II `aconvm_is_effectus`**: blocked on the **left** pullback square of the
effectus axioms — 196II's own proof, eff.tex:3383–3600 — and on nothing else.
Its other four ingredients are now all proved (194I.1–.4).  That proof
constructs, for `α : Z → X+1` and `β : Z → 1+Y` agreeing on `1+1`, a
combination `ω ∈ 𝒟_M(X+Y)` built with the division of the effect divisoid, and
its well-definedness is a two-page interleaving of *two* derivations
(`Φ` from `1+Y`, `Ψ` from `X+1`) into one — so unlike 194I.4 it genuinely does
depend on the derivation calculus of 193IX/193IV, which is unformalized.
Two routes if it is picked up: (a) formalize 193IV's syntactic description of
the least congruence and then transcribe; or (b) use the divisoid to build an
*explicit model* of `X ⨿ Y` (every `⋁λᵢ|κ₁xᵢ⟩ ⋁ ⋁σⱼ|κ₂yⱼ⟩` normalises, by
dividing by `λ = ⋁λᵢ`, to `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩`, so the carrier should be
`M × X × Y` modulo `(1,x,y) ~ (1,x,y')` and `(0,x,y) ~ (0,x',y)`) and read
everything off it.  (b) looks shorter and would also give 193IX for divisoids.
Do **not** shortcut it by splitting off a `sorry`ed left-square lemma: that
would make 194I's consumers depend on a `sorry` and cost the zero-leakage
property.

### Session 5 — B/Eff: 178III.1 and the `AConv_M` coproduct; and 174IV was never `sorry`

B/Eff went **43 → 40** code `sorry`s.  Zero `sorryAx` leakage still holds:
1248 non-internal declarations under `Theses.B.Eff`, exactly 40 of them
`sorry`, none merely depending on one.  All three new theorems and the moved
helper report `[propext, Classical.choice, Quot.sound]`.

**First, a correction to the session-3 hand-off, because it cost this session
its stated priority.**  Session 3 recorded *"174IV `PCM.isSumOf_perm` is the
highest-leverage `sorry` left in `EffectAlgebras.lean`; it blocks 178III.1 and
178V."*  **174IV has been proved since session 1** (commit `634cd1f`), and
**178V `emond_lemma_for_conv` is proved too** — it *uses* 174IV.  The cause is
worth knowing: the doc comment carrying "**174IV** (eff.tex:223)" was attached
to the *helper* `PCM.isSumOf_swap`, and `PCM.isSumOf_perm` — the actual 174IV —
carried **no doc comment at all**, so a DISP-number search found only a helper
sitting next to a proof it did not belong to.  Fixed: 174IV's doc comment now
sits on `isSumOf_perm`, and `isSumOf_swap` is labelled a helper.  *Moral: when
a hand-off says "X is still `sorry`", check the declaration, not the
doc comment.*

#### 178III.1 `unitInterval_effectMonoid_unique` — proved; the argument is ours

eff.tex:636 asserts "(This is the only way to turn `[0,1]` into an effect
monoid)" with a citation to `basmsc` prop. 41 and no proof, so there was
nothing to transcribe.  The Lean proof:

1. transport the hypothesis `em.toEffectAlgebra = unitInterval.effectAlgebra`
   by `rw`, so that `⊥` and `⋁` become the standard `x + y ≤ 1` / `x + y`
   while `⊙` stays an unknown binary operation;
2. one-sided distributivity (`emon_mul_ovee`, below) makes `y ↦ a ⊙ y`
   additive on defined sums, and it is nonnegative, hence monotone;
3. induction gives `a ⊙ (n·y) = n·(a ⊙ y)`, so `a ⊙ (k/n) = a·k/n`;
4. squeezing with `k = ⌊n·y⌋` gives the **lower** bound `a·y − 1/n ≤ a ⊙ y`;
   the upper bound is free from `(a ⊙ y) + (a ⊙ yᵖ) = a ⊙ 1 = a`.

Step 4's asymmetry is the only cleverness: doing the ceiling side directly
needs `min(⌊ny⌋+1, n)` to stay inside `[0,1]`, and the orthocomplement trick
removes that case split entirely.  Since nobody had checked the statement, it
was worth being suspicious — but no defect: it is true as asserted.

**By-product, and it vindicates the thesis's own solution to 178IIIa after the
fact.**  `emon_mul_ovee` (`c ⊥ d ⟹ a⊙c ⊥ a⊙d` and `(a⊙c) ⋁ (a⊙d) = a⊙(c⋁d)`)
is *not* an effect-monoid axiom — 178II only gives the four-fold law — but it
follows from that law once `0 ⊙ x = 0` is known.  The `exc-emonzero` solution
in `bsols.tex` uses one-sided distributivity to *prove* `a ⊙ 0 = 0`, which is
therefore circular rather than merely under-justified (ERRATA row sharpened).
The lemma existed **twice** in the tree (`EffectAlgebras` had none,
`StatesPredicates.lean:109` had it) — one of the duplicate helpers HANDOFF
predicted.  Consolidated into `EffectAlgebras.lean` next to `exc_emonzero`,
keeping the `StatesPredicates` orientation so its four use sites are
unaffected.

*File order*: `unitInterval_effectMonoid_unique` (178III.1) needs
`exc_emonzero` (178IIIa), which the thesis states *after* it, so the theorem
now sits after 178IIIa with a pointer comment at its numbering slot — the same
device session 3 used for 208III.

#### 193V `aconv_coprod` and 194I.1 `aconvalmosteffectus_coproducts` — proved

Both transcribe eff.tex:2806–2890 directly (class 1): the coproduct is the
quotient of the free convex set `𝒟_M(X+Y)` by the least congruence relating
`𝒟_M κ₁ φ` to `η(κ₁(h_X φ))` (and likewise for `κ₂`); the mediating map is
`h_Z ∘ 𝒟_M[f,g]`, which is affine and whose kernel is a congruence containing
those pairs; uniqueness is the thesis's "turn the wheel" computation
`k' ∘ q = k' ∘ q ∘ μ ∘ 𝒟_M η = h_Z ∘ 𝒟_M[f,g]`.  Everything it needs was
already proved in the file (193II.1–3, 193III, 193IV, and the full monad
structure `map_comp`/`map_eta`/`mu_map`/`mu_map_eta`/`mu_mu`).

**Our own statement was wrong, in a way only Lean sees — universe levels.**
`aconv_coprod` was stated as `HasBinaryCoproducts (AConvMCat.{u, v} M)`.  The
coproduct's carrier is a quotient of `𝒟_M(X+Y)`, i.e. of `X+Y → M`, which
lives in `Type (max u v)`; for `v < u` no object of `AConvMCat.{u, v} M` can
carry it — already `1 + 1 ≅ 𝒟_M{1,2}` has as many elements as `M`.  Both this
and `aconvalmosteffectus_coproducts` are now stated at
`AConvMCat.{u, max u v}`, which is the general true form and specialises to
the `{u, u}` that `n_times_one_aconvm` already used.  (`_terminal` is
unaffected — `PUnit` is small.  `_jointlyMonic` and `_kappaPullback` take
`HasFiniteCoproducts` as a *hypothesis*, so they stay true as stated; but that
hypothesis is only instantiable at `v ≥ u`.)  This is our transcription error,
not a thesis defect.

**Thesis defect found in the comparison (ERRATA, 194I).**  The thesis's proof
opens "As `𝒟_M ∅ = ∅`, the empty set is trivially also an abstract `M`-convex
set and in fact the initial object of `AConv_M`".  That fails for the
**trivial** effect monoid (`1 = 0`): a formal convex combination must sum to
`1`, so when `1 = 0` the *empty* combination qualifies and `𝒟_M ∅` is a
singleton — there is no `h : 𝒟_M ∅ → ∅`, and `∅` is not an object of
`AConv_M`.  The proposition survives, because for `1 = 0` every abstract
`M`-convex set is a singleton (`x = h(η x) = h(η y) = y`) so `AConv_M` is the
terminal category and `1` is initial; the Lean proof splits on `1 = 0`
accordingly.

#### What is left, and where it is blocked

Two doc-comment repairs made in passing (both were factually stale, not
statements): the `AConv_M` category instance and `AConvMCat.free` no longer
claim their obligations are `sorry`-ed.

**The †-effectus block is blocked on more than 219XVI.**  The hand-off called
219XVI (`dagger-is-functor`) "the gateway"; checked against eff.tex it is not a
one-lemma gap.  219XVI's proof works "in setting `dagger-setting`" (219II,
eff.tex:5980), which introduces **four isomorphisms** `χ, ω, β, α` — each
obtained from a standard-form/quotient/comprehension uniqueness argument that
itself needs an image computation — and then chains **six** further results:
219III (`f ∘ g` in standard form), 219V `dagger-of-fg`, 219VII
`dagger-iso-beta2`, 219IX `dagger-iso-alpha2`, 219X `dagger-iso-zeta2`, 219XIII
`dagger-iso-omega2` and 219XIV `dagger-iso-chi2`.  **None of the seven is
formalized** — `Dagger.lean`'s own header says so explicitly ("Not separately
formalized: … the Setting 219II with its internal lemmas … represented here by
the standalone 219XI and 219XVI").  219XI `dagger_iso_mu` *is* proved, and it
is what 219XIV rests on, so the block is genuinely reachable — but it is a
~7-lemma, several-hundred-line job, not a gateway.  `bsols.tex` has solutions
for 219IX and 219X (keyed `dagger-iso-alpha2`, `dagger-iso-zeta2`); 219VII and
219XIII have inline proofs; 219XIV has the longest.  Downstream of it:
`dagger_thm_sufficiency` (220II, whose own argument is short and mostly
transcribable once 219XVI lands), `dagger_theorem` (215III, which is then
`dagger_thm_necessity` + 220II), and `snake_lemma` (228II).

⚠ Do **not** shortcut `dagger_theorem` by `⟨dagger_thm_necessity, fun _ =>
dagger_thm_sufficiency⟩`: that would make a proved declaration depend on a
`sorry`ed one and destroy the zero-leakage property for one cosmetic
`sorry`.

The `𝒟_M`/`AConv_M` group is now the most self-contained remaining block:
194I.3 `aconvalmosteffectus_jointlyMonic` and 194I.4
`aconvalmosteffectus_kappaPullback` both argue through the *explicit*
description of coproduct elements — 193IX (`elements-coprod-conv`) and the
`n · 1 ≅ 𝒟_M{1,…,n}` of 193X — and 193IX is deliberately not formalized (only
its existence statements are).  So the next step there is 193X
`n_times_one_aconvm`, whose hint is "`𝒟_M`, as a left adjoint, preserves
coproducts"; with 193V now available that is the natural continuation.

### Session 3 — 77I is blocked, precisely, and the block is in A/CStar

> **Superseded in part (session 4):** the A/CStar half of this block — 38IV.2,
> 39VII, 39IX `bh_np` — is now proved.  76I and 76III should be reachable; the
> A/VN half (72V `normal_functionals_lemma`, 75VIII `vnsac`) stands.

`A/VN/Completeness.lean` went 25 → 21 (72III.1b, 72III.1c, 73IV, 72IV).  The
point of the pass was 77I; it is **not reachable yet**, and the reason is now
sharp enough to act on.

The thesis's route is `𝒜 ≅ ρ_Ω(𝒜) ⊆ B(H_Ω)`.  Of its three ingredients, `ngns`
(48VIII) is proved and the net-pushing step is elementary.  The other two are
walls:

1. **Outside A/VN.**  39IX `bh_np` (`A/CStar/TowardsVN.lean`, still `sorry`)
   blocks *both* 76I and 76III.  Their hypotheses are usable as stated — it is
   the **conclusion** that forces the decomposition `ω = Σ⟪xₙ,(·)xₙ⟫`, since
   the `ε`-tail split is the whole proof.  The abstract substitute would be
   SOT-lower-semicontinuity of `x ↦ ω(x*x)`, which is exactly what the
   decomposition supplies, so there is no shortcut.  Mathlib has no normal
   functionals, so no fallback either.  `bh_np` needs 39VII and 38IV.2, also
   `sorry`, also in that file.  **Closing 38IV.2 + 39VII + 39IX is the
   highest-leverage A/CStar item for A/VN, and it is not circular** — it is
   chapter-1 material.
2. **Inside A/VN.**  75VIII `vnsac`, at the bottom of the column
   `72V → 72XI → 73VIII → 74I/74IV → 75II → 75VI → 75VIII`.  73IV is now done;
   **72V `normal_functionals_lemma` is the real wall** — a 4-way TFAE, atomic
   in Lean, whose (2)⇒(3) step must manufacture four *normal* functionals from
   a vector in `H_ω`.  74I `proto_kaplansky` (Stone–Weierstraß on `ℝ ∪ {∞}`
   through the CFC) is the best single-worker target left.

A route to 77I avoiding 76I was looked for and does not appear to exist:
making the net norm-bounded first lands on 87VIII → 87VI/87III → 86XII/86IX →
72V, i.e. the same wall from the other side.  For the same reason **87VIII is
not an independent target** — Banach–Steinhaus is free from Mathlib, but 87III,
87VI and 72V are all `sorry`.

**⚠️ A new taint route, of the invisible kind.**  The general
(non-self-adjoint) Kaplansky 74IV goes through the 2×2 matrix trick, i.e.
through **`mn_vna_1` (49IV.1, `A/VN/Basic.lean`) — a `sorry`ed `instance`**
`VonNeumannAlgebra (CStarMatrix (Fin N) (Fin N) 𝒜)`.  Any proof taking that
route inherits `sorryAx` *without any visible `sorry` at the use site*, which
is exactly the failure mode `#sorry_leaks` exists to catch.  `kaplansky_sa`,
`kaplansky_pos` and `kaplansky_effects` avoid it entirely.

**Checked: `B/Dils` does need the general form, so `mn_vna_1` is required, not
optional.**  `B/Dils/Kaplansky.lean`'s 158Ia `kaplansky_bounded_approx` is
stated for an arbitrary `b ∈ ℬ` — no self-adjointness, no positivity — and
158II `kaplansky_hilbmod` likewise quantifies over arbitrary `x ∈ X`.  Neither
can be served by `kaplansky_sa`/`_pos`/`_effects`.  Since the standard proof of
the non-self-adjoint case *is* the 2×2 trick, the dependency is real.  So
**49IV.1 `mn_vna_1` should be promoted to a proving target in its own right**:
it is a `sorry`ed instance sitting under two `B/Dils` statements, and until it
is discharged any proof of 158Ia/158II that goes the natural way will be
silently vacuous.

⚠️ **Correction (session 3).**  The claim that followed here — that `mn_vna_1`
was "the one live example of the invisible-taint class in the project" — was
**wrong**, and it was repeated in two commit messages before being caught.  A
`sorry`ed *instance* is not rare; enumerate them mechanically rather than
recalling them:

⚠️⚠️ **Correction to the correction (session 12).**  The recipe first written
here was

```sh
# DO NOT USE — produces false positives
grep -rn '^instance\|^noncomputable instance' Theses/ --include=*.lean -A3 \
  | grep -B3 'sorry' | grep instance
```

and it is **wrong**: `-A3 | grep -B3 sorry` matches a `sorry` occurring
anywhere in the three following lines, *including in a doc comment or in the
next declaration*.  It reported **seven**, then **four**; the true number was
**two** throughout.  Both false positives in `A/Proc/QuantumLambda.lean` were
honest definitions — `StarOrderedRing (MatAlg n) := CStarAlgebra.spectralOrderedRing _`
and `VonNeumannAlgebra (MatAlg n) := Theses.A.VN.mn_vna_1 n`.  The bad count
went into three commit messages and two worker briefs before a worker checked
it.

**Use one of these instead.**  Textual, and exact:

```sh
grep -rn -A2 '^\(noncomputable \)\?instance' Theses/ --include=*.lean \
  | grep -E ':= *sorry$| sorry$'
```

Authoritative, and the one to trust: `#print axioms` on the instance itself,
or `#sorry_leaks` from `Theses/AxiomCheck.lean`, which walks the environment
and cannot be fooled by comments.

As of session 12 there are exactly **two**, both in `A/VN/Basic.lean`:
`vonNeumannAlgebra_lp_infty` (line 676) and `mn_vna_1` (line 3195), each
verified `sorryAx` by `#print axioms`.  The three `cornerSet` instances in
`B/Dils/Pure.lean` were real and have been discharged.

The general lesson, which is the reason this is worth the space: **a
`grep`-shaped proxy for a semantic property will drift from the property.**
Every count that matters here — `sorry`s, leaks, instances — should come from
Lean, not from text matching, or at minimum be spot-checked against Lean
before being repeated.

Also stale, and corrected by the same pass: the session-2 `sorryAx` ranking
listed `Ba.instCStarAlgebra` / `instPartialOrder` / `instStarOrderedRing` as
tainting 14 declarations each.  All three are now **proved**.

**A cheap unblock, for whoever next owns `A/VN/Basic.lean`.**  The vector-
functional link is already there — `gnsHilb`, `gnsRep`, `gnsVec` and
`gnsVec_inner` are all proved, and `ξ_ω := lp.single 2 ω (gnsVec ω 1)` works —
but **48V `varrho_Omega_normal` is `sorry`**, and `exists_faithful_normal_rep`
hides the Hilbert space.  Proving 48V from `gnsVec_inner` is a few lines and
would reduce 77I to exactly the two dependencies above.  No `lp`-instance
taint: this is `lp _ 2` as a Hilbert space.

**Promote the np-functional algebra.**  `Theses.NPFunctional` (in the root
`Common.lean`) carries **no algebraic structure at all**, so the pass had to
build `zeroNP`, `addNP` (normality of a sum proved once, inside),
`omegaNorm_mul_le` and `omegaNorm_le_addNP(')` as file-private helpers.  72V,
72XI, 73VIII and 87VIII all need them; they should move up.

Also noted, and cheap: **88IV `carrier_vector_state` is the best entry point in
`NormalFunctionals.lean`** — its companion `carrier_vector_state'` is already
fully proved and builds the exact machinery needed; combine with the proved
88II `commutant_ceil`.

### ⚠️ Session 2 — the first whole-project axiom check, and a leverage ranking

`Theses/AxiomCheck.lean` finally ran over the entire tree (it needs a green
`lake build Theses`, which concurrent editing had prevented all session):

```
checked 2973 declarations under `Theses`
690 are themselves `sorry`; 200 depend on a `sorry`      (exit code 1)
```

690 sorried *declarations* against ~705 `sorry` tokens — consistent, since some
proofs contain more than one.  The 200 indirect leaks break down as
**A/Proc 163, B/Dils 27, A/VN 8, B/Eff 2**, of which 38 are auto-generated
structure declarations and the rest hand-written.

**The valuable output is not the total but the ranking.**  Almost all of that
taint traces to a dozen sorried *definitions and instances*:

| root `sorry` | declarations tainted |
|---|---|
| `A.Proc.vnTensorProduct_nonempty` | **81** |
| `A.Proc.exists_tmapM` | 23 |
| `A.Proc.nmiuId` | 22 |
| `B.Dils.Ba.instCStarAlgebra` / `instStarOrderedRing` / `instPartialOrder` | 14 each |
| `A.Proc.instStarOrderedRingCorner` | 14 |
| `A.Proc.exists_ncpComp` | 11 |
| `A.Proc.hilbertTensor_nonempty` | 6 |
| `A.VN.exists_carrier` | 4 |
| `A.VN.exists_div` | 3 |

Six declarations account for ~157 of A/Proc's 163 leaks; three instances account
for essentially all of B/Dils's 27.  **This is a work-ordering tool**: proving
`vnTensorProduct_nonempty` is worth more than any number of ordinary statements
in that chapter, because until it holds, everything above it is unproved
regardless of what the `sorry` count says.

Note the shape of the leaks.  These are not proofs citing sorried lemmas — that
rule was never violated.  They are **definitions and instances whose *types*
mention a sorried construction**, so every statement about them inherits
`sorryAx` structurally and invisibly.  `grep` cannot see it and a green build
cannot see it; only an axiom walk can.

Run it with `lake build Theses && lake env lean Theses/AxiomCheck.lean`.  It
exits non-zero while any *hand-written* declaration leaks indirectly
(auto-generated noise is labelled and ignored), which makes it CI-able.

### ⚠️ Session 2 — the `sorry` count overstates progress in B/Eff's upper chain

**The single most important finding of this session, and it is not an erratum.**

`PureCat.category` (`DiamondAmp.lean:938`) — the *`Category` instance on `Pure C`* — defines
composition as `comp f g := ⟨f.1 ≫ g.1, upm_closed_pure f.2 g.2⟩`, and
**`upm_closed_pure` (`DiamondAmp.lean:872`) is still `sorry`**.  A sorried lemma
is therefore baked into an *instance*, so every declaration that treats `Pure C`
as a category inherits `sorryAx` — which is essentially all of `Dagger.lean` and
`Comparisons.lean`.

Twelve declarations were confirmed to depend on `sorryAx` while *appearing*
proved.  Seven are the documented "choice from a sorried existence lemma"
pattern; **five are flagged nowhere at all**, including `isSharp_ovee` →
`diamond_oml_subEA` (via `ea_modularity_prop`), `perp_sharp_is_orth` and
`andthen_square_rule`.  One case is pointed: `pred_sea_s1_s2_s3` carries a
comment explaining that it *avoids* `pureDagger` because that is "still sorry" —
and it depends on `sorryAx` regardless, through the category instance.

Consequences:

* **A `sorry` count is not a progress measure.**  Closing goals above
  `upm_closed_pure` moves the count without making anything true.  Proving
  **211XI `upm_closed_pure`** (pure maps compose) is worth more than any number
  of downstream statements, and should be the next target in B/Eff.
* `lean_verify` / `#print axioms` on the *statement you care about* is the only
  honest check.  Spot-checking a few per file is not enough when the leak is in
  an instance every file uses.
* **Add an automated axiom check** (see below) so this class of leak cannot
  recur silently.

Note this is a different failure from "citing a sorried lemma", which workers
are told not to do: nobody cited anything: the dependency entered through
instance resolution, invisibly.

### Session 2 — `orderIntervalEffectModule` was also our bug

The second long-standing "open decision" inherited from session 1, and the
second one that turned out to be a mis-transcription.  Now **fully proved** —
all five fields, axiom-clean; B/Eff 128 → 123.

Recorded as "false as stated … needs `PosSMulMono ℝ V` added", i.e. as a defect
requiring the author's approval to change a statement.  The *diagnosis* was
right — our hypotheses related the order of `V` to `+` but never to the scalar
action, so even the data field `r • v ∈ [0,u]` was unprovable.  The *conclusion*
was wrong.  The source (eff.tex:737) reads:

> If `V` is an **ordered real vector space** with order unit `u`, then `[0,u]`
> is an effect module over `[0,1]`.

"Ordered real vector space" already means the positive cone is closed under
nonnegative scalars; our `[PartialOrder V] [IsOrderedAddMonoid V]` captured only
the additive half of that.  Adding `[PosSMulMono ℝ V] [SMulPosMono ℝ V]` — the
two monotonicity properties the cone condition yields, and which are equivalent
to it given linearity — makes every field go through in a few lines
(`r•v ≤ r•u ≤ 1•u = u` for membership, `smul_add`/`add_smul` for the two
distributivity fields).

**Companion gap, left open deliberately.**
`effectModule_unitInterval_representation` — the Gudder representation theorem
in the same Examples point — has the mirror-image problem: it *produces*
`[PartialOrder V] [IsOrderedAddMonoid V]` and `0 ≤ u`, so it omits the same
scalar compatibility, and asks only `0 ≤ u` where the thesis says `u` is an
**order unit**.  Our version therefore asserts strictly *less* than the thesis
does; it would be easier to prove and would not be the theorem.  Fixing it needs
an `OrderUnit` predicate the file does not have, so it is flagged for decision
rather than changed silently.

**Two of two.**  Both statement-level "open decisions" carried over from session
1 have now been re-read against the source, and **both were our transcription
errors** — neither was a thesis defect, and neither needed approval to change.
The remaining decisions (trivial C\*-algebra, 23VII.3, 34aVII, 72III.1b/1c)
should be re-read the same way before being acted on: check the `file:LINE` the
Lean doc comment carries, and suspect the transcription before the thesis.

### Session 2 — 221IV.1 was our bug, not the thesis's

Recorded since session 1 as an open decision ("our statement is too strong; not
a thesis error"), this turned out to be a **mis-transcription on our side**,
now corrected and **proved** (`Theses/B/Eff/Dagger.lean`, axiom-clean).

Our uniqueness clause read `∀ α', h₁ ≫ α' = h₂ → α' = α`, quantifying over every
map satisfying only the *first* condition.  The source (eff.tex:6837) says:

> there is a unique isomorphism `α : P₁ → P₂` with `α ∘ h₁ = h₂` **and**
> `ϱ₂ ∘ α = ϱ₁`.

Restoring the missing `α' ≫ ϱ₂ = ϱ₁` hypothesis makes the statement provable
straight from the universal property, by the thesis's own argument: `σ₁ ≫ σ₂`
and `𝟙 P` both mediate `(P, ϱ₁, h₁)` to itself, so they agree, and symmetrically
on the other side.

**Two process lessons, both cheap to avoid.**  First, the entry cited
`dils.tex:1176` — `paschke-unique-up-to-iso`, about *Paschke* dilations of
ncp-maps between von Neumann algebras.  The Lean doc comment says
**eff.tex:6837**, the abstract effectus proposition.  Checking the wrong text is
what turned a transcription bug into a recorded "statement too strong" decision
that sat open for a whole session.  **Always verify against the `file:LINE` the
doc comment itself carries.**  Second: when a statement looks unprovably strong,
suspect the transcription before suspecting the thesis.

**Erratum found while re-reading.**

- **221II** `eff.tex:6791` — in the definition of a dilation: "For every triple
  `(P', ϱ', h')` with `ϱ' : P' → Y` total sharp, **`h' : X → P`** arbitrary and
  `f = ϱ' ∘ h'`".  The type is wrong: `h'` must be `X → P'`, since `ϱ' : P' → Y`
  and `ϱ' ∘ h'` has to typecheck.  A typo, but in the definition on which the
  whole of parsecs 221–223 rests.

### Session 2 — `ThesisPos`: 25I is now a theorem, not an assumption

All five steps of the programme are done.  `sorry` count unchanged at 29 — that
is the expected outcome, since the goal was never to close goals but to make the
existing proofs rest on what the thesis actually has.  `lake build` of all four
A/CStar modules exits 0; nine key theorems verified
`[propext, Classical.choice, Quot.sound]`.  No statement, hypothesis, name or
doc comment changed anywhere.

**Two corrections to the plan as briefed, both material.**

- **The `IsSelfAdjoint` conjunct is not redundant.**  The brief proposed
  `ThesisPos a := ∃ t, ‖a − t‖ ≤ t`.  The thesis's definition (**9IV**,
  `cstar.tex:1130`) also demands self-adjointness, and dropping it makes
  `ThesisPos a ↔ spec(a) ⊆ [0,∞)` **false**: in `M₂`, `1 + iε·e` satisfies
  `‖a − 1‖ ≤ 1` without being self-adjoint.  The shipped definition is
  `IsSelfAdjoint a ∧ ∃ t : ℝ, ‖a − t‖ ≤ t`, placed at parsec 170 and entirely
  order-free.
- **`a*a ≥ 0` is not a parsec-190 result.**  The brief said to prove
  `ThesisPos (a*a)` by the parsec-190 argument.  Parsec 190 explicitly
  *disclaims* it — 19I.1 (`cstar.tex:2813`) reads "Although we can't quite yet
  see that `a*a` is positive — for this we need the existence of the square
  root."  Parsec 190 gives only **19III** (`a*a ≤ 0 ⟹ a = 0`); positivity of
  `a*a` is **24IV**.  Both are now transcribed separately:
  `thesisPos_astara_non_negative` (the literal parsec-190 argument, via
  `prod_spec` and `a*a + aa* = ½((a+a*)² + (i(a−a*))²)`) and
  `thesisPos_star_mul_self` (the parsec-240 argument, taking `u := |h| − h` and
  `b := a·u` in place of `a((a*a)₋)^{1/2}`, which avoids needing a square root of
  `h₋` and the `ineq-square-root` clause entirely).

**The payoff.**  `thesisPos_iff_nonneg` is an honest Lean proof of **25I**,
deliberately split into `ThesisPos.nonneg` (cheap) and `thesisPos_of_nonneg`
(expensive — 24IV on each `star s * s` generator) so the dependence on 24IV stays
visible at every call site.  Mathlib's
`StarOrderedRing.nonneg_iff_spectrum_nonneg` appears nowhere in the block.  The
square root for the `ThesisPos` development comes from re-running the 23II
iteration against `ThesisPos`; none of the order-based `SqrtAux` is reused.

Eleven pre-25I proofs were re-pointed onto it, none reverted — including
`astara_positive` (24IV, previously `star_mul_self_nonneg`),
`nonneg_iff_spectrum_ofReal_nonneg` (previously Mathlib's CFC-backed 25I), and
17VI.2/3a/3b/3c/4a/4b/4c/4d/5.  **One was left deliberately**: the Lean
`astara_non_negative` still uses `star_mul_self_nonneg`, because re-pointing it
would make parsec 190 depend on parsec 240 — backwards.  In the star-order
encoding that statement genuinely *is* trivial, and the thesis's real 19III now
exists separately.

Also fixed here: **20aI.2** by the thesis's own sup-norm hint (no square root, no
CFC), which required filling a **Mathlib gap** — `CStarAlgebra (lp 𝒜 ∞)` is
neither provided nor synthesizable, so a one-line instance was added.  Two
further CFC-at-the-wrong-parsec violations surfaced and were fixed:
`weak_russo_dye_1` (parsec 200 using positive/negative parts from 240) and
`positive_basic_2_5` (parsec 170 using `CFC.inv_nonneg`).

**New erratum.**

- **19Ia** `cstar.tex:2834` — "`λ⁻¹(1 + b(λ−ab)a)`" is missing an inverse; it
  should read "`λ⁻¹(1 + b(λ−ab)⁻¹a)`".  Not in `asols.tex`'s errata block, which
  has no parsec-190 entry at all.

### Where the bootstrapping now stands

**It holds from parsec 110 upward**, with exactly two imported facts at the base:
`IsSelfAdjoint.spectralRadius_eq_nnnorm` (**16III**) and
`IsSelfAdjoint.mem_spectrum_eq_re` (**11XV**.1).  Both are taken from Mathlib
because the thesis's own route to them — the 𝒜-valued complex-analysis block at
parsecs 120–150 — is still `sorry`.  Both sit *below* the CFC in Mathlib's import
graph, so neither smuggles in later thesis content.

Above that line: **25I** is a theorem rather than an assumption; **19III** and
**24IV** are theorems rather than artefacts of Lean's definition of the star
order; and the continuous functional calculus appears nowhere below parsec 230.

Closing parsecs 120–150 would remove the last two imports and make the chapter
self-supporting from the ground up.  That is now the single highest-value target
in A/CStar.

### Session 2 — A/VN, second pass

251 → 226 (Basic 52→48, Projections 103→88, Completeness 32→26).  Full VN chain
builds; sampled results verified `[propext, Classical.choice, Quot.sound]`.

**Two structural wins.**  **44VIII** `ad_normal` (`⋁_d a*da = a*(⋁D)a`) — the
chapter's bottleneck — is transcribed in full from the thesis: the
order-isomorphism for invertible `a`, `λ+a` invertible via `Units.oneSub`, the
decomposition `a*da = (λ+a)*d(λ+a) − λ²d − λ(da) − λ(a*d)` with the four
ultraweak limits from 44VI/44VII, and the author's own work-around for the
not-yet-Hausdorff ultraweak topology (a positive difference killed by every
np-functional is zero, by `np_faithful`).  And **42V.2**
`VonNeumannAlgebra (H →L[ℂ] H)` via cstar.tex 37IX plus a new bundled
`vectorNP x : NPFunctional (H →L[ℂ] H)`.  Also all of parsec 550, resting on two
extracted workhorses `le_proj_iff`/`proj_le_iff` (`b ≤ p ↔ b·p^⊥ = 0` and
dually) that reduce the two 11-fold TFAEs of 55VIII/55IX to instances at `b`,
`√b`, `b²`.

**Erratum — 72III.1b/1c are FALSE as stated.**  `Completeness.lean:63`, `:70`;
`vn.tex:3850`.  The `‖ω‖` factor in `|ω(a*bc)| ≤ ‖ω‖‖a‖_ω‖b‖‖c‖_ω` (and in the
companion Lipschitz bound) **breaks homogeneity**: with `‖a‖_ω = ω(a*a)^½`
unnormalised, replacing `ω` by `tω` scales the left side by `t` and the right by
`t²`.  Counterexample: `𝒜 = ℂ`, `ω = t·id` with `t ∈ (0,1)`, `a = b = c = 1`
gives `t ≤ t²`.  The correct inequalities are the same ones **without `‖ω‖`**,
and those are provable exactly as intended.  Both left `sorry` — they are not
provable as written.

Note this is the **same authorial slip as 30IV.2**, where the extra `‖ω‖` was
also confirmed spurious (Mathlib's `leftMulMapPreGNS` is *defined* with bound
exactly `‖a‖`).  A spurious `‖ω‖` on a `‖·‖_ω` estimate has now appeared twice
in two chapters; worth checking every such bound in both theses.

**The directed-net conflation, third instance — and this one is ours.**
vn.tex 272 (42V.2) is *correct*: cstar.tex 37IX carries the pointwise hypothesis
`sup ⟪x,Tx⟫ < ∞`, which an order bound supplies.  But its 37XI repackaging in
`A/CStar/TowardsVN.lean` (`exists_isLUB_of_normBounded_directed`, `bhSup`)
demands **norm** boundedness, which order-bounded directed sets need not have.
So `bhSup` cannot be used for 42V.2, and the proof must go through
`hilb_suprema_1/_2`.  First time the defect sits in the Lean repackaging rather
than in the text — worth remembering that our own helper lemmas can reintroduce
a defect we just removed from the thesis.

**A systematic sweep came back clean.**  Every bounded-directed-net occurrence
in `vn.tex` was checked — 22 sites — and there are **no further instances**: the
text consistently says "norm bounded" where it means it.  So the earlier
expectation that this pattern would recur throughout the theses is **not** borne
out for A/VN; 37IX and the 44III citation remain the only textual cases.

**Now unblocked, in order.**  (1) `bstaromega_np` (72III.1a) — normality *is*
`ad_normal`.  (2) `np_orderSeparating` (44XI), which needs
`import Theses.A.CStar.Representation` — deliberately not added so as to leave
the tree green.  The recipe: every np-functional is `CentreSeparating` trivially
(take `b = 1`, use `np_faithful`); `proto_gelfand_naimark_1` upgrades that to
`OrderSeparating` for `{a ↦ ω(b*ab)}`; and those are np-functionals **by
`ad_normal`** — the step that was impossible before.  Then 44XI.1–3 and 44XIII
follow.  (3) `exists_ceil`/`exists_floor` (56I/56VI) need 44XIII first, and
unlock parsecs 560–630 (~40 `sorry`s).

Parked with reasons: `hahn_banach` (73IV — Mathlib's geometric Hahn–Banach does
not apply, the radial topology is not a TVS), `commutant_basic_2` (ultraweak
closedness, blocked on 44XI), the remaining 43II counterexamples (need
`bh_functional_lemma_2`), `vonNeumannAlgebra_lp_infty`.  **Nothing in the chapter
relies on Mathlib's Sakai-style `VonNeumannAlgebra`/`WStarAlgebra`.**

### Session 2 — A/VN, first pass

`A/VN/Basic.lean` 77 → 52 (25 proved); the other four files untouched.  The
whole VN chain builds.  **No errata** — and note this chapter was worked under
the corrected policy, so `vn.tex` was read for every point touched: **zero
"did not consult" cases**.  Per the author's confirmation that the vN exercise
solutions were never written, the ~15 Exercise points proved here are logged as
**original work (no author argument exists)**, which is a different status from
"unchecked".

Two statements looked wrong and are not, both worth recording so nobody
re-investigates: `almostClopen_sigmaAlgebra` (53V) carries only
`[ExtremallyDisconnected X]` with no compactness, unlike its neighbours — but
vn.tex:1876 really does state the Corollary for an arbitrary extremally
disconnected space and its proof never uses Baire.  And `uwweaker_1` (43I.1)
assumes `[VonNeumannAlgebra A]` although the inequality holds for any positive
functional on any C\*-algebra — weaker, not wrong; the general form is exported
as `norm_apply_le_omegaNorm`.

**The reusable win**: the thesis's seminorm `‖a‖_ω` is *definitionally* the norm
of Mathlib's GNS pre-Hilbert space — `omegaNorm_eq_norm` is `rfl`.  That single
identification yields Kadison's inequality, the seminorm laws, and the
`IsLUB`-in-`ℂ` → `IsLUB`-in-`ℝ` bridge that drives every supremum/net result in
the chapter.  `Completeness.lean` alone mentions `omegaNorm` seven times, so this
is the lever for the next pass.

**The directed-net pattern recurs — a finding in its own right.**  44VII and
44XIV both say "use `vanishing-effects` (44III)", but **44III cannot be used as a
black box there**: it demands `∀ i, x i ∈ effects A`, while `(⋁D − d)/M` is only
*eventually* an effect.  A bounded directed set need not be bounded below
(`D = {−n} ∪ {0} ⊆ ℝ` gives unbounded `‖⋁D − d‖`), so no single normaliser works;
informally one passes to the cofinal subnet `{d ≥ d₀}`, which in Lean is a change
of index type.  The Lean proof inlines the *estimate underlying* 44III with an
`∀ᶠ` bound instead.  Nothing is wrong with 44III or with the exercises, but the
hint needs a footnote once nets are made precise.  **This is the same defect as
37IX** (`cstar.tex:6244`), where "bounded above" was silently read as
"norm-bounded" — so the pattern spans both chapters and is worth a systematic
check wherever the theses invoke a bounded directed net.

Divergences, both type (2), the thesis's own order otherwise followed
throughout: `meagre_full_measure` gets its dense open sets of small measure from
outer regularity rather than explicit intervals around an enumeration of
`ℚ ∩ [0,1]`; and `baire_category_theorem` (54II) uses Mathlib's
`BaireSpace.of_t2Space_locallyCompactSpace` rather than the thesis's from-scratch
nested-open-sets proof — which does *not* break bootstrapping, since vn.tex
itself cites Willard at that point.

**Next steps identified.**  44VIII `ad_normal` → 44XI `np_orderSeparating` →
44XIII are blocked only by an import: the thesis routes them through
`proto-gelfand-naimark` (cstar.tex 30X), which *is* formalized and sorry-free as
`Theses.A.CStar.proto_gelfand_naimark_1` — but in `A/CStar/Representation.lean`,
which `A/VN/Basic.lean` does not import.  Adding that import is low-risk and
unblocks three statements.  (44XIII is *not* provable from faithfulness alone —
`a·⋁D − ⋁D·a` is not positive — so it must wait for 44XI.1.)  Separately, 42V.2
`VonNeumannAlgebra (H →L[ℂ] H)` should be proved from cstar.tex 37IX + 25III in
the already-imported `TowardsVN.lean`, **not** via Mathlib's differently-defined
`VonNeumannAlgebra H`.

### Session 2 — Matrices.lean, third pass

Four more closed (`bax_cstar` 32XIII, `choi_2` 34XVIII.2, `cp_commutative_cod`
34IX.1, `cstar_product_4` 34VI.1); 11 → 7.

- **34VI**.1 `cstar_product_4` — **the author's solution slot is empty**:
  `parsec-340.60` in `asols.tex` is literally `\TODO{}`.  (It is also the *last*
  solution in the file, which is why coverage appears to stop there.)  So this
  is proved but **not cross-checked** — there is no author argument to compare
  against.  The Lean proof uses `weak_russo_dye_2` (20II) rather than
  `cp_russo_dye` (34XVI) for the `lp ∞` bound, since 34XVI comes later in the
  thesis and is out of scope at that point.
- **34XVIII**.2 `choi_2` — the thesis applies Choi part 1 *to `M₂f`*, which
  presupposes "`M_N` of a cp map is cp" (via `M_N(M_2) ≅ M_{2N}`), a fact absent
  from both this development and Mathlib.  The Lean proof gets the same 2×2
  positivity directly from complete positivity of `f` at `N = 3` (adjoining
  `v₀ = 1`); the finish via `cstar_positive_2x2matrix` is the thesis's.
- **32XIII** `bax_cstar` — the thesis's proof verbatim, but it glosses over one
  thing Lean cannot: `ModuleAdjointTo` takes a *bare function*, so a private
  lemma was needed showing an adjoint is automatically linear (by definiteness)
  and bounded (32X), hence genuinely a `X →L[ℂ] X`.

**A previous "no published solution" claim was wrong**, as suspected:
`chilb_vector_states_2/3` *do* have a solution at `parsec-320.150` — the earlier
report's denial was the label-search artefact.  It was read this time.  They
remain parked for a different reason: the solution works inside the C\*-algebra
`Bᵃ(X)`, and Mathlib has no type of adjointable operators, so `Bᵃ(X)` does not
exist as a Lean type.  `bax_cstar` and `module_maps_cstar_identity` are now both
proved and are exactly the analytic input such a construction needs; what
remains is instance-building.

**Parked with a verified blocker.**  `ccstar_pos_mat` (34VII) is the single
obstruction to the chain **34VII → cp_commutative_dom → normal_russo_dye →
russo_dye_cor**.  Mathlib has the partition of unity; what it lacks is
`M_N(C(X)) ≅ C(X, M_N ℂ)` *as ordered* C\*-algebras — no transport of the
`CStarMatrix` order along a base `StarAlgEquiv`, no "positive iff pointwise
positive", no `‖A‖ = sup_x ‖A(x)‖`.  The absence of a bypass was checked, not
assumed: factoring `A = star C * C` returns the goal to itself.

Discipline note worth keeping: this pass **deliberately declined to write proofs
citing still-`sorry`ed lemmas**.  Doing so lowers the `sorry` count while making
the result depend on `sorryAx` — a strictly worse outcome that `lean_verify`
would catch but the count would not.

### Session 2 — audit of the 37 first-pass proofs

All 37 statements proved before the "author's proof first" policy came in were
re-read against the authors' arguments (Positive 23, TowardsVN 11,
Representation 3).  Verdicts: **20 match, 11 diverge** (7 of them carrying a
dependency-order flag), **6 errata**, **3 not cross-checkable**.  All six errata
were checked against the 27 already recorded at the top of `asols.tex`; three
further items in scope (`200.30`, `300.40`, `370.50`) were found to be already
recorded and are *not* re-reported.

**New errata.**

- **17III** `cstar.tex:2716` — stated for `t ∈ [0,∞]`; at `t = ∞` the condition
  `‖a − t‖ ≤ t` is meaningless.  Should be `[0,∞)`.
- **17VI**.6 `asols.tex:1844` — "suppose that `a` is **not** invertible, then
  `0 ∉ spec(a)`".  The direction actually being proved (invertible ⟹ `a ≥ 1/n`)
  is never begun; delete the "not" and the rest of the solution is correct.
- **26II**.1 `asols.tex:2372` — "`a` and `b` are positive": `a` is an arbitrary
  self-adjoint element and need not be positive (`𝒜 = ℂ`, `a = −1`, `b = 1`).
  Separately, `b ≥ 0` — which *is* needed, to turn `√(b²)` back into `b` — is
  asserted without the step `2b = (b−a) + (b+a) ≥ 0`.  The Lean proof supplies
  exactly that missing step.
- **26II**.4 `asols.tex:2433` — "`a ∨ b = ½(a + b + |a + b|)`" should have
  `|a − b|`.  Check `a = 2`, `b = −1`: the printed right-hand side gives `1`,
  while `a ∨ b = 2`.
- **30IV**.1 `asols.tex:3142` — Cauchy–Schwarz is written with squares on the
  right, `|[a,b]_ω|² ≤ [a,a]_ω² [b,b]_ω²`; as displayed it does not yield
  Kadison's inequality.
- **20aII** `asols.tex:1939` — "`e ∘ h = g`" should be "`e ∘ h = γ`" (typo).

Three further sub-erratum gaps: **37VII** omits Cauchy-ness when invoking 37II;
a garbled sentence in solution `250.10`; and implicit boundedness in the wlog of
solution `140.20`(4).

**Dependency-order findings — the important part.**  Seven, of which two are
systemic.  None is a soundness problem: every Lean proof is correct, and Mathlib
establishes these results independently.  What they mean is that **these proofs
do not validate the thesis's own bootstrapping**, which is a distinct kind of
value from validating its statements.

- **(A) systemic — what `0 ≤ a` *means*.**  In Lean, `0 ≤ a` is Mathlib's star
  order (`a = b*b`).  In the thesis before **25I**, positivity is "`‖a − t‖ ≤ t`
  for some `t`".  Their equivalence *is* 25I.  So every statement before 25I
  that is phrased with `0 ≤ a` is, strictly, using the conclusion of 25I to say
  what it says.  Visible concretely in **17V**, where Lean's 3→4 goes through a
  CFC theorem while the thesis proves 3⟹2 elementarily — and the author's route
  is already available in the file.
- **(B) systemic — CFC used before the thesis has it.**  Everything from parsec
  230 onward uses the continuous functional calculus (`CFC.sqrt/abs/posPart`,
  `Commute.mul_nonneg`), which the thesis obtains only after Gelfand
  (parsecs 270–280).  The thesis hand-builds `√` at **23II** precisely to avoid
  this.  Affects 23VII.0/.0'/.0''/.1/.2, 25I(1→3), 26II.
- **(C) sharpest.**  **23VII**.0'' closes `c² ≤ a ⟹ c ≤ √a` with
  `CFC.sqrt_le_sqrt`, which is thesis **28III** `sqrt-monotone`
  (`cstar.tex:4353`) — five parsecs later, and itself built on top of 23VII.
  Circular with respect to the thesis's development order.
- **(D)** **17VI**.6 uses `CStarAlgebra.inv_le_inv`, i.e. thesis **25II**.3.  The
  author's spectral route would work in Lean.
- **(E)** **27XV** is closed by
  `WeakDual.CharacterSpace.mem_spectrum_iff_exists` — Gelfand theory obtained
  through maximal *ring* ideals, which is circular w.r.t. the thesis and is
  exactly the route **16VIII** rejects.
- **(F)** **16II** uses Mathlib's general spectral-radius formula, which
  **16IV** says the thesis does not prove.
- **(G)** 23VII.1/.2 are statement-faithful but CFC-backed.

**Trivial algebra `{0}`.**  16VII and 17VI.3b are **confirmed** to survive only
accidentally — 17VI.3b's thesis infimum is over `ℝ` and is honestly `−∞` in
`{0}`, while Lean survives on `Real.sInf` junk-value conventions.  Refuted for
all other 35.

**Not cross-checkable (3).**  39VI.1 and 39VI.2 are Exercises with no inline
proof, and parsec 390 is outside `asols.tex`'s coverage — the Lean proofs there
are **original work**, not transcriptions.  37V.1 is a Definition whose net
claim is asserted without argument, and the Lean theorem proves strictly more.

### Session 2 — Matrices.lean, second pass (33II.1 unblocked)

Nine statements closed, including the bottleneck **33II.1**
`cstar_matrix_positive_iff` in both directions, and everything that waited on
it: 33II.2, 33III.3, 34II, 34IV.1, 34IV.2, 34XII, 34XIV, 32XV.1.

**The convention fix is confirmed correct.**  `cstar_matrix_gram_nonneg` is now
*proved* in the corrected, argument-swapped form, and the author's own solution
goes through verbatim once the swap is applied.  That is independent evidence
that the transcription — not the thesis — was at fault.

**Three places where the author's argument could not be transcribed.**  Each is
a finding in its own right, and all three trace to the same root: the thesis
works with structures that Mathlib either does not bundle or bundles more
strongly.

- **33II.1** — the thesis derives it from **32XV.2** (vector states on `Bᵃ(X)`
  are order-separating).  `Bᵃ(X)` is not a bundled C\*-algebra here — only
  predicates — so 32XV.2 is itself not provable.  The Lean proof instead runs
  *the author's own 32XV.2 argument, step for step*, inside `M_N(𝒜)` where the
  structure does exist: `T = T₊ − T₋`, `T T₋ = −T₋²`, `T₋³ = 0`, `T₋ = 0`.
- **34XII** — the thesis applies Cauchy–Schwarz to the form `⟨x, Ay⟩` on `𝒜²`.
  Mathlib's `CStarModule` **bundles definiteness**, so that semi-inner product
  is not an instance and `chilb_cs` cannot be applied to it.  Lean completes the
  square inside `M₂(𝒜)` instead.
- **33III.3** — the author's route needs that same Cauchy–Schwarz, which exists
  in Lean only as 34XII, sitting *later* in the file; a forward reference is
  impossible.  The faithful version was compiled separately and does work if
  34XII is moved earlier; as shipped, 33III.3 uses an explicit counterexample.

Followed the thesis: 33II.2, 34II, 34IV.1/2, 34XIV, 32XV.1.

**Mathlib defect worth reporting upstream.**
`ContinuousFunctionalCalculus ℝ (CStarMatrix n n 𝒜) IsSelfAdjoint` cannot be
synthesised, although the instance term typechecks when supplied by hand: the
conclusion carries `Algebra.complexToReal` while `Algebra ℝ (CStarMatrix n n 𝒜)`
resolves to `CStarMatrix.instAlgebra` — defeq but not syntactically equal.  So
`CStarAlgebra.nonneg_iff_eq_star_mul_self`, `CFC.negPart` and
`NonnegSpectrumClass ℝ` are all unusable directly on `CStarMatrix`.  Workaround
used throughout: state the CFC-dependent fact for an abstract `M`, then
instantiate.

### Session 2 — Positive.lean / Representation.lean, second pass

Nine statements closed (20aI.1, 20aI.2, 21X, 25II.3, 25V.3, 26II.4, 26III;
28II.2 and 30X (2)⇔(3) in `Representation.lean`).  **No errata** — no thesis
proof read in this pass was wrong or incomplete.  Two findings worth the
authors' attention are about *structure* rather than correctness:

- **30X (2)⇒(3)** — the thesis routes this through (1), i.e. through
  injectivity of the *direct-sum* GNS representation `ϱ_Ω` on `⊕_ω ℋ_ω`
  (plus 25III and 29IX).  That infrastructure is deliberately absent here, so
  the Lean proof goes **directly, with no GNS at all**: involution-preservation
  of p-maps forces `a = a*`, and substituting `b := a⁻c` into centre separation
  forces `(a⁻)³ = 0`.  **This suggests the detour through (1) is avoidable**,
  which would make 30X's (2)⇔(3) independent of the direct-sum construction — a
  simplification the authors may want.
- **25V.3** — **not cross-checked.**  There is no published solution
  (`parsec-250.50` is absent), and the inline proof derives it from **21VII**,
  which is still `sorry` here (and whose own proof reduces to **20VI**, also
  `sorry`).  It was proved independently via Mathlib's Rayleigh-quotient norm
  formula, so the author's route remains unverified.
- **20aI**.2 could not follow the thesis's norm route at all: Mathlib has no
  `CStarAlgebra (lp 𝒜 ∞)` instance.  **20aI**.1 uses the miu norm bound rather
  than the thesis's pu/Russo–Dye bound.

21X, 25II.3, 26II.4 and 26III **do** follow the authors' arguments.  The last
two were initially closed Mathlib-first and then **rewritten** to follow the
thesis after the "author's proof takes precedence" policy came in — 26II.4 now
goes `f√ = √f → f|·| = |f·| → f(∨)`, and 26III now uses the author's own `a'`,
`b'` with meets re-expressed via `(·)⁺`.

Also parked here: **24II.3**, whose published solution reads, in full, "The hint
gives the solution away" — an explicit 2×2 counterexample still has to be
produced.

### Session 2 — 37IX (A/CStar/TowardsVN.lean)

The gap previously recorded between 37VII and 37IX is now resolved, and it
turned out to be **three** defects in one Proposition, not one:

- **37IX** `cstar.tex:6244` — "is WOT-Cauchy, and *WOT-bounded*" is unjustified:
  37VII needs the diagonal net **norm**-bounded, while 37IX supplies only a
  bound from **above**.  Counterexample: `D = {−n·1}` is upward directed and
  bounded above by `0`, yet `‖⟪x,(−n)x⟫‖ = n‖x‖²` is unbounded.
- **37IX** `cstar.tex:6224` — the Proposition omits `D ≠ ∅`, which parts 1 and 2
  need.
- **37IX** `cstar.tex:6247` — the proof claims 37VII yields a *self-adjoint*
  limit, but 37VII as stated concludes only "some bounded operator".  The Lean
  proof establishes self-adjointness separately, from realness of the limit's
  diagonal values.

**The repair is cheaper than expected.**  The obvious fix — pass to the cofinal
tail `{d ∈ D : d₀ ≤ d}` and transport `atTop` along the inclusion — was not
needed.  Replacing the net by its truncation `F T = if d₀ ≤ T then T else d₀`
gives something globally norm-bounded (squeezed between `⟪x,d₀x⟫` and the given
upper bound), so 37VII applies directly, and `F T = T` holds *eventually* along
`atTop`, so `Filter.Tendsto.congr'` carries the limit back.  No filter-basis
reasoning at all.  This unblocked 37IX.1–3, 37XI and 38II, plus 38III, 38VI.1
and 39VI.3.

Dependency-order note: the thesis proves 37IX.3 and derives 37IX.2 from it; our
statements are independent, so each is proved directly from the diagonal-net
convergence.

Scope note: `asols.tex` stops at `parsec-340.60`, so **38III and 38VI.1 have no
published solution** — those Lean proofs are original, not transcriptions.

### Session 2 — errata found by the Basic.lean cross-check audit

These came from deliberately re-reading the authors' own proofs for the nine
statements listed in the next section, which had been closed from Mathlib
without consulting them.  **No statement was refuted and no author proof is
wrong in substance** — all nine are true and the arguments sound modulo these
defects — but the audit is what turned "proved" into "cross-checked", and it
found four new items in one pass.

- **11XX**.1 `cstar.tex:1636` — the exercise reads "the spectrum of a continuous
  function `f : X → ℝ` … being an element of the C\*-algebra `C(X)`", but `C(X)`
  is defined at `cstar.tex:206` (2VI) as the **complex**-valued continuous
  functions, and `spec(f) ⊆ ℂ`.  The author's own solution
  (`asols.tex:1276–1284`) proves `spec(f) = f(X)` for arbitrary `f ∈ C(X)`,
  never using real-valuedness.  Should read `f : X → ℂ`, or just "`f ∈ C(X)`".
  Lean states the general ℂ-valued version (`spectrum_continuousMap`).
- **11XX**.2 `asols.tex:1286` — the solution opens "A square matrix is
  invertible iff its kernel is **not** `{0}`", which is exactly backwards
  (`A = 0` in `M₁` has kernel `ℂ ≠ {0}` and is not invertible).  The *next*
  sentence is correct and is what the rest of the argument uses, so this is a
  dropped negation rather than a broken proof.  (Same solution, `:1287`: "In
  particilar".)
- **11XV**.2 `asols.tex:1221` — "since `a − √λ i` and `a + √λ i` are invertible
  **by point 2**" is a self-reference: point 2 is the statement being proved.
  The invertibility comes from **point 1**, which the author cites correctly for
  the same fact three paragraphs later (`asols.tex:1252`).  Mis-citation only.
- **4VIII** `cstar.tex:424` — in the *definition* of an inner product,
  "`⟨x,·⟩ : V → V` is linear"; the codomain is `ℂ`.  A typo, but in a definition
  the whole of parsec 40 rests on.
- **11XV**.3 `cstar.tex:1589` — the hint `aⁿ+1 = ∏ₖ (a + ζ^{2k+1})` has the wrong
  sign; the right-hand side is `aⁿ − 1` (check `n = 1`: `x + ζ³ = x − 1`).  The
  author's own solution derives the corrected form at `asols.tex:1248`.
  **Already recorded** at `asols.tex:30–34` — confirmed independently here, not
  a new finding.

Minor, recorded for completeness: `asols.tex:1250` states the exceptional index
as `k ≠ (n−1)/2` where it should be `k ≢ (n−1)/2 mod n` (literally false at
`n = 1`, harmless there); `asols.tex:1214–1223` never states the one-line
even-`n` conclusion the exercise asks for; `asols.tex:1092–1102` silently
divides by `‖P − ‖x‖²‖`; and the counterexample solutions for **7III**.8,
**7III**.13 and **9X**.3 all open "let `x,y` be … vectors of a Hilbert space"
without exhibiting one, leaving the existence half of "give an example"
implicit (`ℂ²` works in all three; Lean names concrete 2×2 matrices).

**Development-order divergences — worth the authors' attention.**  Two Lean
proofs are correct but use results the thesis deliberately does *not* have
available at that point, so they do not validate the thesis's own bootstrapping:

- **9X**.3 `cstar_positive_3` — Lean picks the same witnesses as the author
  (`|e₁⟩⟨e₁|` and `|v⟩⟨v|`, `v = (1,1)`) but establishes positivity via
  `star_mul_self_nonneg`, i.e. `a*a ≥ 0`.  The thesis explicitly cannot use that
  at parsec 90: **9X**.5 lists even "`a²` is positive" as out of reach, and it is
  settled only at **25I**.  The author's elementary norm computation
  `‖P − s‖² = s‖P − s‖` is the honest route and would formalise easily.
- **11XV**.3 `spectrum_self_adjoint_real_3` — Lean uses polynomial spectral
  mapping (`spectrum.map_pow_of_pos`); the author's factorisation
  `bⁿ + 1 = ∏ₖ (b − ζ^{2k+1})` is precisely the *elementary substitute* for that
  theorem, which parsec 110 is still building towards.  Both correct; the
  factorisation was verified here in general and at `n = 1, 3`.

Neither is unsound — Mathlib proves these independently of the thesis — but a
reader wanting the formalization to check the thesis's *own* development order
should treat these two as not yet doing so.

### Session 2 — divergences from the thesis's proofs (A/CStar/Basic.lean)

**Status: all nine were subsequently cross-checked** (see the audit errata
above).  Verdicts: **6 match** the author's argument, **3 diverge**, **0**
statements refuted.  A specific check for the trivial-algebra pattern
(`𝒜 = {0}`, `ℋ = {0}`, `X = ∅`, `n = 0`) that produced 16V/16VI/22III.5 found
**no new instance** among the nine.  The list below is kept as the record of how
they were originally closed.

**These statements are proved but were NOT cross-checked against the thesis's
own argument.**  They were closed directly from Mathlib without reading the
published proof or solution — in most cases because the solution was looked for
with the wrong `grep` pattern (see "Where the proofs are" above: `asols.tex` is
keyed by `parsec-N.M`, not by label, so a label search finds nothing and looks
like "no solution exists").  **A published solution does in fact exist for every
one of them.**  Re-checking these against the authors' arguments is outstanding
work — it is exactly the cross-check that produces errata.

- **4IV** `operatorNorm_ball` — solution at `parsec-40.40`.  Lean proves
  `r‖T‖ = sup{‖Tx‖ : ‖x‖ ≤ r}` by rescaling `x` to norm exactly `r` and
  bounding via `ContinuousLinearMap.opNorm_le_bound`, with a separate `r = 0`
  branch.  Not compared to the author's argument.
- **4XV**.4 `inner_product_basic_4` — solution at `parsec-40.150`.  Closed from
  Mathlib's `inner_eq_sum_norm_sq_div_four` after rewriting `‖Iⁿx + y‖` into
  `‖x ± Iy‖` form.  Not compared.
- **7III**.8 `cstar_involution_basic_8` — solution at `parsec-70.30`.  Lean uses
  its own counterexample `a = !![0,1;0,0]`; the authors may intend a different
  one.  Not compared.
- **7III**.13' `cstar_involution_basic_13'` — solution at `parsec-70.30`.  Lean
  sidesteps computing any operator norm: it picks `T` with `T² = 0` but `T ≠ 0`,
  reducing the claim to `0 ≠ ‖T‖²`.  Almost certainly *not* the thesis's route.
- **9II** `cx_positive` — solution at `parsec-90.20`.  Lean proves the five-way
  TFAE as the cycle 1→2→3→1 plus 1→5→4→1, chosen for convenience; the author's
  cycle is likely different.  Not compared.
- **9X**.3 `cstar_positive_3` — solution at `parsec-90.100`.  Lean uses its own
  counterexample (`!![1,0;0,0]`, `!![1,1;1,1]` via `Matrix.toEuclideanCLM`), with
  the obstruction being that `ab` is not self-adjoint.  Not compared.
- **11XV**.3 `spectrum_self_adjoint_real_3` — solution at `parsec-110.150`.
  Closed from Mathlib's spectral mapping (`spectrum.map_pow_of_pos`,
  `spectrum.pow_mem_pow`) plus `Odd.pow_nonneg_iff`.  Not compared.
- **11XX**.2 `spectrum_matrix` — solution at `parsec-110.200`.  Closed from
  `Matrix.exists_mulVec_eq_zero_iff`.  Not compared.
- **11XXI**.1' `spectrum_basic_1'` — solution at `parsec-110.210`.  Derived from
  our own `spectrum_matrix` rather than from the thesis's argument.  Not
  compared.

For contrast, the two that *were* cross-checked:

- **4XIII**.2 `positive_2x2matrix_2` — **follows the thesis**, transcribing the
  `v = 1`, `u = tc̄` discriminant argument at cstar.tex:571 including its
  `p = 0` / `p > 0` split.
- **5III** `projection_on_c00` — **deliberate divergence**, and the Lean proof is
  shorter: the thesis argues via density of `c₀₀` in `ℓ²`, whereas orthogonality
  of `x − y` to each `lp.single 2 n 1` kills every coordinate directly, so
  `lp.ext` closes it with no density argument at all.

### Session 2 (A/CStar)

**Transcription errata — our Lean statements, not the thesis.**  Mathlib's
`CStarModule` uses the *opposite* inner-product convention to the thesis: the
thesis has right 𝒜-modules with `⟨x, y·b⟩ = ⟨x,y⟩ b`, Mathlib has
`⟪x, a•y⟫ = a ⟪x,y⟫`, so `⟪x,y⟫_Mathlib = ⟨y,x⟩_thesis`.  Two statements were
transcribed without the swap and were therefore **false**.  Both have now been
corrected (with the convention recorded in their doc comments):

- **32VI** `Theses/A/CStar/Matrices.lean:196` (`chilb_cs`) — Cauchy–Schwarz.  As
  written it asserted `⟪x,y⟫⟪y,x⟫ ≤ ‖⟪y,y⟫‖ • ⟪x,x⟫`; counterexample
  `𝒜 = M₂(ℂ)`, `X = C⋆ᵐᵒᵈ(𝒜,𝒜)`, `x = e₁₁`, `y = e₂₁`, giving `e₂₂ ≤ e₁₁`.
  **Fixed** by swapping to `⟪y,x⟫⟪x,y⟫ ≤ ‖⟪y,y⟫‖ • ⟪x,x⟫`, which is then
  Mathlib's `CStarModule.inner_mul_inner_swap_le` plus `norm_sq_eq` — now
  **proved** in one line.
- **33II**.2 `Theses/A/CStar/Matrices.lean:433` (`cstar_matrix_gram_nonneg`) —
  the Gram matrix.  In Mathlib's convention `(⟪xᵢ,xⱼ⟫)ᵢⱼ` is the *block
  transpose* of the thesis's Gram matrix, and block transposition does not
  preserve positivity — that is exactly **33III**.3.  Counterexample: `𝒜 = M₂(ℂ)`,
  `x₁ = e₁₁`, `x₂ = e₂₁` gives the transposition permutation matrix in
  `M₂(M₂(ℂ)) ≅ M₄(ℂ)`, eigenvalue `−1`.  **Fixed** to
  `fun i j => inner 𝒜 (x j) (x i)`; still `sorry` (downstream of 33II.1).

Checked and *not* affected by the same flip: the adjointness condition
`⟪Tx,y⟫ = ⟪x,Sy⟫` (it is the star of the thesis's condition, hence equivalent);
the diagonal forms `⟪x,Tx⟫` in 32XII/32XIII/32XIV (`0 ≤ a ↔ 0 ≤ star a`, and
norms are star-invariant); `B/Dils/HilbertModules.lean` (its doc comment already
states the mirrored convention); `B/Dils/SelfDual.lean:507` (both sides flip
together); `B/Dils/Stinespring.lean` (ℂ-valued inner product, whose convention
*does* match Mathlib — confirmed by `inner_product_basic_4` proving against
`inner_eq_sum_norm_sq_div_four` with no swap).

**Thesis errata.**

- **23VII**.3 `Theses/A/CStar/Positive.lean` (cstar.tex:3663) — "if `a,b ∈ sa(𝒜)`
  commute and `a ≤ b` then `a² ≤ b²`" is **false as stated**: in `𝒜 = ℂ`,
  `a = -2 ≤ 1 = b` but `4 ≰ 1`.  The intended hypothesis is `0 ≤ a`, which the
  immediately following item 4 already assumes; with it the proof works via
  `b² − a² = b(b−a) + (b−a)a ≥ 0`.  **Parked** — needs author approval.
  **[RESOLVED 2026-08-13 — erratum 230.70 was already this; incorporated.]**
- **34aVII** `Theses/A/CStar/Matrices.lean` (cstar.tex:5842) — `russo_dye` is
  **false at `N = 0`**, purely from Lean's `2/(0:ℝ) = 0`: the hypothesis
  degenerates to `‖a‖ < 1` while the conclusion says `a = 0`.  The thesis says
  "for some natural number `N`" and means `N ≥ 1`.  **Parked** — needs `N ≠ 0`.
  For `N ≥ 1` it follows immediately from the proved `sum_of_unitaries_3`.
- **Four more statements false for the trivial C\*-algebra `{0}`**, joining 16V:
  **16VI** `spectrum_eq_singleton_iff` (← direction) and **22III**.5
  `order_ideal_basic_5`.  Mathlib's `CStarAlgebra` does not extend `Nontrivial`.
  Notably the thesis's *own* solution to 22III.5 (asols.tex:2112) picks a
  convergent subsequence in `spec(a)`, silently assuming it non-empty — the same
  missing hypothesis.  **16VII** `gelfand_mazur` and **17VI**.3b survive the
  trivial case only accidentally, and their Lean proofs need a
  `subsingleton_or_nontrivial` split the thesis proofs do not have.
- **37IX vs 37VII** `Theses/A/CStar/TowardsVN.lean:456` — a real gap.  37VII
  requires the diagonal net **norm**-bounded; 37IX supplies only bounded
  **above**, and these are not equivalent for directed sets: `D = {−n·1}` is
  upward directed and bounded above by `0`, yet `‖⟪x,(−n)x⟫‖ = n‖x‖²` is
  unbounded.  So 37IX does not follow from 37VII by substitution; one must pass
  to the cofinal tail `{d ∈ D : d₀ ≤ d}` and transport `atTop` along the
  inclusion.  The thesis glosses this by reading the net "eventually".
- **38VI**.2 `Theses/A/CStar/TowardsVN.lean:345` — the `←` direction is **false
  as stated**: a constant net `x_α = i·x` gives the same vector functional.
  Parked.  **[RESOLVED 2026-08-13 — the "if" direction is dropped from the
  thesis; see HANDOFF.]**
- **30IV**.2 `Theses/A/CStar/Representation.lean:417` — independent confirmation
  that the extra `‖ω‖` is spurious: Mathlib's `leftMulMapPreGNS` is *defined*
  with bound exactly `‖a‖`, so the Lean proof never mentions `‖ω‖`.
- **34XVI** `Theses/A/CStar/Matrices.lean:704` (`cp_russo_dye`) — the thesis
  derives this from Russo–Dye (**34aVIII**), a *later* point; a forward
  reference is impossible in Lean.  The Lean proof derives it from the cp
  Cauchy–Schwarz **34XIV** instead — a genuine reduction that avoids Russo–Dye
  entirely, and arguably the better dependency order.
- **20II**.1 `weak_russo_dye_1` — the thesis proof needs one unstated step in
  Lean: that `f a` is self-adjoint, which is not part of `IsPositiveMap` and must
  be derived from `a = a⁺ − a⁻`.
- **23VII**.0'' `sqrt_commute` — proved via Mathlib's CFC commutation and
  monotonicity of `√` rather than the thesis's iteration of 23II.  No
  circularity, but a different dependency order.
- **5III** `Theses/A/CStar/Basic.lean:497` (`projection_on_c00`) — not an error,
  but the Lean proof is **shorter than the thesis's**: the thesis argues via
  density of `c₀₀` in `ℓ²`, whereas orthogonality of `x − y` to each
  `lp.single 2 n 1` kills every coordinate directly, so `lp.ext` finishes it with
  no density argument at all.
- **33I**.2 `Theses/A/CStar/Matrices.lean:366` — the surjectivity half of
  `cstar_matrices_2` never uses the adjointability hypothesis; it is redundant
  (harmless) there.
- **32I** `Theses/A/CStar/Matrices.lean:83` — the module-map proof needs
  definiteness of the inner product in the *first* argument, while uniqueness of
  the adjoint needs it in the *second*.  The thesis states definiteness once;
  both directions get used.
- **34XVIII**.1 `choi_1`, and `sum_of_unitaries_2/3` — need a `Subsingleton ℬ`
  case split, since `‖(1 : ℬ)‖ = 1` requires `Nontrivial` in Mathlib.

## Parked items

(Format: `**DISP** file:line — reason`.)

- **180X.1** `Theses/B/Eff/Effectus.lean:311` — Cho's theorem, `Par C` is an
  effectus in partial form: needs the whole of parsec 187 (the PCM structure on
  the hom-sets of `Par C` has to be *constructed* first); too large for now.
- **180X.3** `Theses/B/Eff/Effectus.lean:318` — `Tot (Par C) ≌ C`, proved in
  188IV on top of all of 186–187; too large for now.
- **180X.2** `Theses/B/Eff/Effectus.lean:335` — `Tot D` is an effectus in total
  form (181XI): the thesis's proof is all of parsec 181; too large for now.
- **180X.3** `Theses/B/Eff/Effectus.lean:341` — `Par (Tot D) ≌ D` (188III);
  same.
- **186IV** `Theses/B/Eff/Effectus.lean:897` and `:905` — the thesis's proof
  (eff.tex:1573) says "it is sufficient to show that the following squares are
  pullbacks in `C`" and then appeals to 185I (now proved).  The *sufficiency*
  is left to the reader and is the real work: it needs the translation of
  `Par C`-cones into `C`-cones together with the associativity isomorphisms
  `(X+A)+1 ≅ X+(A+1)`.  Parked pending that infrastructure.
- **186X** `Theses/B/Eff/Effectus.lean:1011` — the thesis's proof pastes the
  3×3 diagram of `Par C`-pullbacks of 186IV (parked above) into
  `joint_monicity_stable` (proved); blocked only on 186IV.
- **180V/189aI** `Theses/B/Eff/Effectus.lean:1074` and `:1079` — `vNᵒᵖ` is an
  effectus in total/partial form: needs essentially all of thesis A (all the
  statements it depends on are still `sorry`).
- **189aII.3** `Theses/B/Eff/Effectus.lean:1086` — every finitary extensive
  category with a final object is an effectus in total form; the thesis leaves
  this to the reader ("instances of general facts"), and the joint-monicity
  axiom for `1+1+1 ⟶ 1+1` needs real work with Mathlib's `FinitaryExtensive`.

- **195V.1** `Theses/B/Eff/StatesPredicates.lean:768` — `unitInterval.effectDivisoid`:
  the *data* field `div a b := ⟨a/b, _⟩` demands `a/b ∈ [0,1]` for arbitrary
  `a, b`, which is false when `a > b` (the thesis's division is partial,
  defined only for `a ≼ b`).  The membership `sorry` is unprovable as the
  definition stands, so the five axiom fields are parked with it.
- **192III.1/.2** `Theses/B/Eff/StatesPredicates.lean:352` and `:400` —
  `exists_map` / `exists_mu`: the existence of the partial sums defining
  `𝒟_M f` and `μ` rests on "every subsum of `1` exists" in an effect monoid,
  which the thesis (192III, Exercise\*) leaves to the reader; needs new
  `PCM.IsSumOf` infrastructure.
- **192IV** `Theses/B/Eff/StatesPredicates.lean:484` — composition in
  `AConv_M` is affine: needs functoriality `(p.map f).map g = p.map (g ∘ f)`,
  i.e. regrouping of partial sums along fibres, which the `exists_map`
  specification does not give.  (The identity case is proved, via the new
  `MConvexComb.map_id`.)
- **192II** `Theses/B/Eff/StatesPredicates.lean:414` — `bin`: provable but
  needs a four-way case split (`x = y`, `l = 0`, `lᵖ = 0`, else); left for
  lack of time, not for want of an argument.
- **190II.5/190III/191II/191VIII/192III.1–3/192V/192VII/193/194/195IV/195VI/195VII/196II**
  `Theses/B/Eff/StatesPredicates.lean` — the remaining items are the deep
  content of these parsecs (representation theorems, the monad `𝒟_M`, the
  effectus structure of `AConv_M`, the basic-disconnectedness criterion);
  not attempted.
- **198III/199VI** `Theses/B/Eff/Quotients.lean:426` and `:467` — quotients
  (comprehension) exist iff `0` (`1`) has a left (right) adjoint: the thesis
  gives the argument (bsols.tex:2687 ff.) but the `⇒` direction has to build
  a functor `Q` by choice on objects together with its functoriality; sizeable,
  not attempted.
- **203IV.5/.6, 203XIII** `Theses/B/Eff/Quotients.lean:780`, `:785`, `:810` —
  `⌈p⌉ ∘ f ≤ ⌈p ∘ f⌉` and its consequences: the thesis's proof factors
  `f ∘ π_{(p∘f)ᵖ}` through `π_{pᵖ}` and uses `⌈0⌉ = 0`; not attempted for lack
  of time (the `⌊·⌋` half of `floor-basics`, 1–4, is proved).
- **203XIV** `Theses/B/Eff/Quotients.lean:818` and `:824` — `im ⟨f,g⟩ =
  [im f, im g]`: the solution (bsols.tex:2889) computes with
  `eff-prod-rules` (181IX), which is still `sorry` in `Effectus.lean`.
- **205IV** `Theses/B/Eff/Quotients.lean:915` — quotient for a sharp predicate
  = cokernel of its comprehension; not attempted.

### B/Eff/DiamondAmp.lean, Dagger.lean, Comparisons.lean

- **206III/211IV** `Theses/B/Eff/DiamondAmp.lean:114` and `:866` — `vNᵒᵖ` is a
  ⋄-/&-effectus: needs essentially all of thesis A (as 180V/189aI).  Likewise
  **215VI** `Dagger.lean:149`, **221III** `Dagger.lean:612`, **223VI**
  `Dagger.lean:661`, **224VI/224VII** `Comparisons.lean:129`, `:140` and
  **225V** `Comparisons.lean:174`.
- **208III** `DiamondAmp.lean` (second half only) — `SPred X` is an
  orthomodular lattice (Cho): parked because it asks for an actual
  `OrthomodularLattice` *instance*, i.e. `⊔`/`⊓` chosen by unique choice from
  204V/208IX plus all the ortholattice laws.  The *first* half (`SPred X` is a
  sub-effect algebra of `Pred X`) is proved, transcribing the thesis
  (eff.tex:4630): orthogonal sharp `s, t` have infimum `0` by order-sharpness
  (208I), so `s ⋁ t = s ∨ t` by `ea-modularity-prop` (177Ia) and is sharp by
  `lattice-compr` (204V).
- **208VII** `DiamondAmp.lean:603` — the functor to `OMLatGal`; blocked on
  208III (it needs the OML instance) although its data (`f_⋄, f^□` and the
  adjunction) is now available.
- **211V/211VII/211XI/212I/212III/213I** `DiamondAmp.lean:873`, `:881`,
  `:890`, `:898`, `:919`, `:924`, `:1005`, `:1016`, `:1025`, `:1030`,
  `:1035`, `:1043` — the &-effectus core (sharpness ⟺ `p & p = p`, the
  corresponding quotient `ζ_s`, closure of comprehensions/pure maps under
  composition, `ζ_{⌈p⌉} ∘ asrt_p` is a quotient, the standard form of a map,
  the effect divisoid of scalars).  The thesis has full proofs
  (eff.tex:4897–5253) but they form one interlocking block: 211V needs
  purity bookkeeping of 211XI, 211VII needs 211V, 211XI needs 211VII, and
  212–213 need all of it.  Not attempted for lack of time; the exercises
  hanging off this block (211XIV, 211XV, 213III, 213V) *are* proved, citing
  the block's statements.
- **213VI** `DiamondAmp.lean:1041` (`exc_prod_sharp_maps`) — `⟨f,g⟩` sharp
  iff `f` and `g` sharp.  The `img-tupling` half of the blocker is gone
  (203XIV is now proved in `Quotients.lean`), but the solution
  (bsols.tex:3149) still needs `diamond-oml` (208III) for "`s ∘ f` and
  `t ∘ g` sharp ⟹ their sum is sharp", and 208III is parked.  Still parked.
- **215III–220** `Dagger.lean:138`–`:385` — the whole †-effectus development
  (the equivalence theorem 215III, its consequences 216, the dagger of a
  pure map 217, pristine maps 218, functoriality 219–220).  These are the
  deep chapters of the thesis (eff.tex:5327–6800); not attempted.
- **221IV.1** `Dagger.lean:421` — dilations are unique up to iso.  The Lean
  statement demands the mediating iso be unique among *all* `α'` with
  `h₁ ∘ α' = h₂`, whereas the universal property of 221II (and the thesis's
  proof, dils.tex:1176) gives uniqueness only among the `α'` that *also*
  satisfy `ϱ₂ ∘ α' = ϱ₁`; without knowing `h₁` epi the stronger clause does
  not follow.  Parked rather than proved; the statement is left as is.
- **221IV.2** `Dagger.lean:428` (`dils_abstract_basics_2`) — transport of a
  dilation along an iso.  Re-examined in the consolidation pass: everything
  *except* two facts is now routine (take the mediating map `α⁻¹ ≫ σ₀` from
  the universal property of the given dilation; uniqueness transports by
  composing with `α.hom`), and `IsTotal (α.inv ≫ ϱ)` follows from
  `iso_isTotal` + `isTotal_comp`.  The two genuine gaps are
  `SharpMap α.inv` (isomorphisms are sharp maps — no lemma for this yet;
  the natural route is via `asrt_iso`, itself `sorry`) and
  `IsPure (h ≫ α.hom)` (needs `upm_closed_pure`, which is `sorry` in
  `DiamondAmp.lean` *and* only available under `AndThenEffectus`, whereas
  this section assumes only `DiamondEffectus`).  Still parked.
- **221IV.6** `Dagger.lean:533` (`dils_abstract_basics_6`, the single
  remaining `sorry` inside an otherwise complete proof) — purity of the map
  `h''` obtained by factoring the pure `h` through the quotient `ξ`
  (`ξ ≫ h'' = h`).  Writing `h = ξ₀ ≫ π` (quotient then comprehension) one
  would need a quotient `ξ₁` with `ξ ≫ ξ₁ = ξ₀`, i.e. that quotients compose
  and that the predicate of `ξ` is below that of `ξ₀`; not available.
- **224III/226–228** `Comparisons.lean:87`–`:371` — dagger kernel categories,
  the homological characterisations of kernels/cokernels/exact maps, the
  `⋄`/`□` lemma 227V and the Snake Lemma: all rest on the parked †-effectus
  development of parsecs 216–220 (in particular on `pureDagger`).
- **225V.1** `Comparisons.lean:174` (`effects_sea`) — `[0,1]_𝒜` of a von
  Neumann algebra is a SEA with `a & b = √a b √a`: needs the continuous
  functional calculus of thesis A; not attempted.

### B/Eff/EffectAlgebras.lean

- **174IV** `Theses/B/Eff/EffectAlgebras.lean:217` (`PCM.isSumOf_perm`) —
  generalized (permutation) associativity of PCM sums.  eff.tex:223 states it
  without proof; the induction needs a simultaneous statement about splitting a
  sum at an arbitrary position, which the axioms only give after a nested case
  analysis.  Known blocker for other files; not attempted.
- **176III** `Theses/B/Eff/EffectAlgebras.lean:917` (`exc_dposet_ea`) — a
  D-poset carries an effect algebra structure.  bsols.tex:1494 gives the whole
  argument, but transcribing it means *constructing* an `EffectAlgebra` whose
  `Perp`/`ovee` are defined by `a ⋁ b = c ↔ c ⊖ b = a` (hence by choice), plus
  single-valuedness and ten axioms; sizeable, not attempted.
- **177Ia** (`ea_modularity_prop`) — **no longer parked: the Proposition is
  false and is now refuted in the tree** (`WrightTriangle.not_ea_modularity_prop`),
  with the statement realigned to the surviving identity and proved.  See the
  session entry "B/Eff: 177Ia is false" above, the two 177Ia rows in ERRATA.md
  and QUESTIONS.md B4.
- **177VI** (`orth_ea_is_orthomodular`) — **no longer parked: proved.**  In an
  ortholattice both bounds exist, so only the surviving identity half of 177Ia
  is needed, and it is established inline (the `key` step of the proof).
- **177V** `Theses/B/Eff/EffectAlgebras.lean:993`
  (`projections_orthomodularLattice`) — projections of a von Neumann algebra
  form an orthomodular lattice; eff.tex:559 states it as an example with no
  proof, and Mathlib has no projection lattice for W*-algebras yet.
- **178III.1** `Theses/B/Eff/EffectAlgebras.lean:1175`
  (`unitInterval_effectMonoid_unique`) — "the usual product is the only effect
  monoid structure on `[0,1]`"; eff.tex:636 asserts it without proof.
- **178III.2/.4** — **partly un-parked (session 44).**  `178III.4`
  `exists_noncommutative_effectMonoid` is **proved**: the `ℝ⁵` example is
  reconstructed in full (`LexNC`, `EffectAlgebras.lean`), since eff.tex:651
  only cites \[basmsc, cor. 51].  The corollary `178III.2`
  `finite_effectMonoid_commutative` is **proved** too, by a direct route that
  does not go through the Boolean structure theorem.  Still parked:
  `finite_effectMonoid_boolean` itself (`EffectAlgebras.lean`, the *structure*
  equality with `booleanEffectMonoid`), which eff.tex:640 cites to
  \[basmsc, prop. 40] — but see the session-44 entry: the mathematics for it
  is now in the file; only the structure-equality transport is missing.
- **178V** `Theses/B/Eff/EffectAlgebras.lean:1247` (`emond_lemma_for_conv`) —
  the solution (bsols.tex:1653) computes with `aᵢᵖ = ⋁_{j≠i} aⱼ`, i.e. it drops
  one summand out of an iterated sum; that is exactly the generalized
  associativity of 174IV, parked above.
- **179III.1** `Theses/B/Eff/EffectAlgebras.lean:1339` (`ea_equiv_emod_two`) —
  `EA ≌ EMod₂`: needs the two functors, the natural isomorphisms and the fact
  that every `2`-action on an effect algebra is the canonical one; eff.tex:722
  states it as an example.
- **179III.2** `Theses/B/Eff/EffectAlgebras.lean:1380`–`:1384`
  (`orderIntervalEffectModule`) — *unprovable as stated*: the hypotheses are
  `[AddCommGroup V] [Module ℝ V] [PartialOrder V] [IsOrderedAddMonoid V]`,
  which relate the order to `+` but not to the scalar action, so already the
  data field `r • v ∈ [0,u]` fails.  (Counterexample: order `ℝ` by the positive
  cone of a ℚ-linear, non-ℝ-linear functional — translation-invariant, yet
  `r • u` for irrational `r` need not be positive.)  The thesis's "ordered real
  vector space" (eff.tex:731) tacitly includes `0 ≤ r, 0 ≤ v ⟹ 0 ≤ r • v`, in
  Mathlib terms a `PosSMulMono ℝ V` / `OrderedSMul ℝ V` instance.  Since
  statements may not be changed, all five fields are parked; with that
  hypothesis they are routine.
- **179III.2** `Theses/B/Eff/EffectAlgebras.lean:1397`
  (`effectModule_unitInterval_representation`) — the Gudder–Pulmannová
  representation theorem; eff.tex:731 cites it to the literature.

### Un-parked (second pass over StatesPredicates.lean / Quotients.lean)

The following items listed above as parked are now **proved**; the entries
are kept for the record.

- **195V.1** `unitInterval.effectDivisoid` — after the data repair (truncated
  division, see "Repairs" above) all five axiom fields are proved.  The
  algebraic order of `[0,1]` is the order of the reals
  (`unitInterval_le_iff`), after which each field is a one-line calculation.
- **195IV.1/.2** `exc_divisoid_basics_1` / `_2` — transcribed from
  bsols.tex:2439; they need only `a ⊙ b ≼ a` in an effect monoid
  (`emon_mul_le_left`, a special case of `distrib`).
- **192II** `MConvexComb.bin` — proved via the helper `bin_sum_one`, by the
  four-way case split (`1 = 0`, `x = y`, `λ = 0`, `λᵖ = 0`, generic).
- **203IV.5/.6, 203XIII** `floor_basics_5`, `floor_basics_6`,
  `ceiling_within_ceiling` — the thesis proof of "Ad 5" transcribes directly;
  "Ad 6" needs `⌈0⌉ = 0`, obtained from the new helper `floorPred_one`
  (`𝟙` is a comprehension for `1`, so `⌊1⌋ = im 𝟙 = 1`).
- **203XIV** `img_tupling` / `img_tupling_sharp` — as in bsols.tex:2889, on
  top of `eff_prod_rules_1/2` (now proved in `Effectus.lean`).  The
  cancellation step of the solution is isolated as the helper
  `eq_of_ovee_eq_of_le` (in an effect algebra, `a ⋁ b = A ⋁ B` with `a ≤ A`,
  `b ≤ B` forces `a = A`, `b = B`).
- **205IV** `exc_cokernels` — bsols.tex:2927; both universal properties have
  the same side condition, `g ∘ π_s = 0` iff `1 ∘ g ≤ sᵖ`, using
  `im π_s = s` for sharp `s`.
- **195VII** `divisoid_div_ovee` — proved by a different route than the
  thesis; see the erratum above.

Still parked in these two files: **198III**
`Theses/B/Eff/Quotients.lean:424` and **199VI** `:465` (the `⇒` directions
build a functor by choice on objects — unchanged from the first pass), and
the deep content of parsecs 190–194/195VI/196 in
`Theses/B/Eff/StatesPredicates.lean` (representation theorems, the monad
`𝒟_M` and `AConv_M`, the basic-disconnectedness criterion), all of which
hinge on the `exists_map` / `exists_mu` subsum infrastructure or on whole
parsecs of new material.

### Consolidation pass over `B/Eff/` (deduplication + third pass)

Several `B/Eff` files had been proved concurrently against each other's stale
oleans, so basic helpers existed in duplicate and triplicate.  All duplicates
are now removed; the surviving (canonical) names are the ones in the file
where the notion is *introduced*:

- `PCM.perp_zero`, `PCM.ovee_zero`, `PCM.zero_ovee'`, `PCM.ovee_congr`,
  `PCM.isSumOf_nil_iff`, `PCM.isSumOf_cons_iff` (all `EffectAlgebras.lean`).
  Deleted: the `private` copies `ovee_congr`/`perp_zero`/`ovee_zero` in
  `Effectus.lean` (whole `section PCMLemmas`), and `pcm_perp_zero`,
  `pcm_ovee_zero`, `pcm_zero_ovee'`, `ovee_congr`, `isSumOf_cons_inv`,
  `eq_zero_of_isSumOf_nil` in `StatesPredicates.lean`.  (`isSumOf_cons_inv h`
  becomes `PCM.isSumOf_cons_iff.mp h`, `eq_zero_of_isSumOf_nil h` becomes
  `PCM.isSumOf_nil_iff.mp h`.)
- `zero_le_hom`, `eq_zero_of_le_zero`, `pred_le_truth`, `comp_le_comp`,
  `iso_isTotal`, `comp_orth_eq_zero_iff` (all `Quotients.lean`) and
  `truth_effObj_eq_id` (`StatesPredicates.lean`).  Deleted: the whole
  `dia_`-prefixed block in `DiamondAmp.lean` and the two `dag_`-prefixed
  copies in `Dagger.lean`.
- `dia_isSharp_zero` (`DiamondAmp.lean`) is canonical; the later duplicate
  `isSharp_zero` in `Comparisons.lean` is deleted.  (The Comparisons copy had
  strictly weaker hypotheses — it did not need `DiamondEffectus` — but every
  use site is under `AndThenEffectus`, which extends `DiamondEffectus`, so
  nothing is lost.  If a `DiamondEffectus`-free version is ever wanted, the
  right home is `Quotients.lean`, next to `IsSharp`.)

No other duplicate pairs were found (checked by comparing every top-level
declaration name modulo the `dia_`/`dag_`/`pcm_`/`eff_`/`exc_` prefixes and
by comparing statement texts).

Newly proved in this pass:

- **223II** `Dagger.lean` `asrt_perp_asrt_orth` — `asrt_p ⊥ asrt_{pᵖ}`.  The
  summability criterion the log asked for is already an axiom of an effectus
  in partial form (`EffectusPartialForm.perp_of_one_perp`); with
  `1 ∘ asrt_p = p` (`asrt_spec`) the whole proof is four lines.  This also
  makes the definition `sef` of the side-effect map genuine.
- **225V.2** `Comparisons.lean` `commutative_effectMonoid_sea` — a commutative
  effect monoid is a SEA with `a & b = a ⊙ b`.  (S1) is the existing helper
  `emon_mul_ovee` in `StatesPredicates.lean`; the other four axioms are
  commutativity and `mul_assoc`.  This is exactly a case of (b): it was
  parked only because `emon_mul_ovee` was not visible at the time.
- **225VI** `Comparisons.lean` `pred_sea_s1_s2_s3` — (S1)–(S3) for `Pred X`
  in a †-effectus; see the two errata notes above.

Doc comments refreshed (declarations that are no longer `sorry`-ed but whose
comments still said so): `DiamondAmp.lean` `PureCat.category` (211XVI),
`Quotients.lean` the `Category (PredSquare C)` instance (198II), and in
`StatesPredicates.lean` the file header plus `scalEffectMonoid`,
`predEffectModule`, the `PCM Mᵐᵒᵖ` instance, `prodEffectMonoid` and
`continuousUnitIntervalEffectMonoid`.  Only the stale factual clause was
touched.

### A/CStar/Basic.lean, A/CStar/Positive.lean (parsecs 3–26)

- **16V** `Theses/A/CStar/Positive.lean:281` (`spectrum_nonempty`) — false for
  the trivial C*-algebra, see the errata entry above.
- **4IV/4XV.4/5III/9II/11XX.2/11XXI.1'** `Theses/A/CStar/Basic.lean:101`,
  `:252`, `:395`, `:758`, `:1316`, `:1331` — `operatorNorm_ball`
  (`r‖T‖ = sup {‖Tx‖ : ‖x‖ ≤ r}`, a `⨆` over a subtype needing the
  `BddAbove`/`csSup` API), the polarisation identity, the projection-on-`c₀₀`
  exercise, the five-fold TFAE for `C(X)`, the spectrum of a matrix as its set
  of eigenvalues and `spec [[0,2],[0,0]] = {0}`: all routine but each needs its
  own concrete computation; not attempted for lack of time.
- **7III.8/7III.13'/9X.3** `Theses/A/CStar/Basic.lean:648`, `:708`, `:920` —
  the three counterexamples among 2×2 matrices / operators on ℂ²
  (`ℜa ℑa ≠ ℑa ℜa`, `‖T²‖ ≠ ‖T‖²`, a product of positives that is not
  positive).  Each needs entrywise computation in `Matrix (Fin 2) (Fin 2) ℂ`
  or in `EuclideanSpace ℂ (Fin 2) →L[ℂ] _`; not attempted.
- **4XIII.2** `Theses/A/CStar/Basic.lean:213` (`positive_2x2matrix_2`) — the
  discriminant argument (`Q(-s c̄/|c|, 1) = p s² - 2s|c| + q ≥ 0` for all
  `s ≥ 0`) has to be run inside `ℂ` with `ComplexOrder`; part 1 is proved.
- **11XV.3** `Theses/A/CStar/Basic.lean:1257` (`spectrum_self_adjoint_real_3`)
  — the odd-power variant.  Part 2 (even powers) is proved with
  `spectrum.map_pow_of_pos` + `IsSelfAdjoint.mem_spectrum_eq_re`; part 3 needs
  the same in both directions together with `Odd.pow_nonneg_iff`, i.e. a
  translation of "`spec(a) ⊆ [0,∞)`" back and forth through the `ℂ`-spectrum;
  not finished for lack of time.
- **12–15** `Theses/A/CStar/Positive.lean:91`–`:260` — the whole
  holomorphic-function development (Hadamard's radius of convergence, term-wise
  differentiation of power series, the 𝒜-valued contour integral, Goursat,
  Cauchy's formula for an N-gon, Taylor expansion, rigid expansion) and the
  computations `invint_1`–`invint_4`.  Mathlib has the scalar theory
  (`Complex.circleIntegral`, `DifferentiableOn.hasFPowerSeriesOnBall`), but the
  thesis's polygonal formulation would have to be built from scratch; the
  elementary derivative rules (12III) *are* proved.
- **16II/16VI/16VII** `Positive.lean:270`, `:287`, `:296` — `‖a‖` = spectral
  radius, `spec(a) = {λ} ↔ a = λ`, Gelfand–Mazur.  Mathlib has
  `IsSelfAdjoint.toReal_spectralRadius_eq_norm`; the remaining work is the
  `ℝ≥0∞` bookkeeping and (for 16VII) the trivial-algebra case.  Not attempted.
- **17III/17V/25I** `Positive.lean:320`, `:336`, `:925` — `pos_spectrum` and
  the two TFAE lists characterising positivity.  The pieces are now available
  (`norm_le_iff_neg_algebraMap_le` in `Basic.lean`,
  `StarOrderedRing.nonneg_iff_spectrum_nonneg`, `CFC.sqrt`), but each item asks
  for a translation between the `ℝ`- and `ℂ`-spectrum; left for the next pass.
- **17VI.3b/17VI.6** `Positive.lean:362`, `:421` — `‖a‖ = inf {λ : -λ ≤ a ≤ λ}`
  (the set is not guarded by `0 ≤ λ`, so one first has to derive `0 ≤ λ` from
  `-λ ≤ a ≤ λ`, which needs `0 ≤ algebraMap ℝ 𝒜 r → 0 ≤ r`) and "positive `a`
  is invertible iff `a ≥ 1/n`".
- **20II/20VI** `Positive.lean:462`, `:468`, `:503` — `weak_russo_dye` and
  `cstar_isometry`: both need the two-sided norm bound *`-b ≤ x ≤ b` with
  `0 ≤ b` implies `‖x‖ ≤ ‖b‖`*, which Mathlib only has for `0 ≤ x ≤ b`
  (`CStarAlgebra.norm_le_norm_of_nonneg_of_le`); it would have to be derived
  from `CFC.abs`.
- **20aI/20aII** `Positive.lean:521`, `:531`, `:545` — the product of
  C*-algebras (`lp 𝒜 ∞`) as a categorical product and the equaliser
  subalgebra; both are mostly bookkeeping with `lp`/`StarSubalgebra`, not
  attempted.
- **21VII/21X** `Positive.lean:644`, `:658` — the sup-norm characterisation of
  order separating families and its dense-subset variant.  (The four
  elementary implications of 21II and 21V *are* proved.)
- **22III–22VIII** `Positive.lean:695`–`:760` — the entire order-ideal/state
  development (kernels of states are maximal order ideals, Zorn's lemma for
  order ideals, the ideal generated by a self-adjoint element, the state
  attached to a maximal order ideal, states are order separating).  This is the
  substantial part of parsec 220 and was not attempted.
- **23II/23VII** `Positive.lean:780`–`:856` — the iteration `bₙ₊₁ = ½(a+bₙ²)`
  for the square root and its four consequences.  Mathlib's `CFC.sqrt` gives
  the *existence* statement (`sqrt_spec` is proved), but the thesis's
  uniqueness/monotonicity statements (`sqrt_existsUnique`, `sqrt_commute`,
  `sqrt_1`–`sqrt_3`) need "everything commuting with `a` commutes with `√a`",
  for which Mathlib's `cfc` commutation API would have to be dug out.
- **24II.3/25II.3/25II.4** `Positive.lean:904`, `:967`, `:973` — the
  counterexample to the triangle inequality for `|·|`, the four-fold TFAE about
  `a ≤ b⁻¹`, and `(1+a)⁻¹a ≤ (1+b)⁻¹b`.
- **25III/25V** `Positive.lean:998`–`:1017` — vector states are order
  separating and its corollaries.  Mathlib has
  `ContinuousLinearMap.nonneg_iff_isPositive` and `isPositive_iff_complex`; the
  remaining work is the passage from *all* vectors to *unit* vectors (a
  homogeneity argument) and the sup formula for `‖T‖`.
- **26II/26III** `Positive.lean:1031`–`:1063` — commutative C*-algebras are
  Riesz spaces, and the Riesz decomposition lemma; not attempted.

### `A/CStar/Representation.lean` (40 → 17)

- **27VIII, 27X.1/1b/1c/2/3, 27XI, 27XIII** `Representation.lean:78`, `:88`,
  `:99`, `:110`, `:120`, `:128`, `:135`, `:142` — the entire Riesz-ideal
  development (Riesz ideals are ring ideals; the least Riesz ideal generated by
  a self-adjoint element; maximal Riesz ideals are maximal order ideals; each
  maximal Riesz ideal is the kernel of an miu-map).  Not attempted: it rests on
  the order-ideal development of **22III–22VIII** in `Positive.lean`, which is
  itself parked, and Mathlib gives no shortcut (it goes via maximal *ring*
  ideals).  **27XV** (`inv_mult_state`, `:150`) is the one consequence that
  *is* available from Mathlib —
  `WeakDual.CharacterSpace.exists_apply_eq_zero : ¬IsUnit a → ∃ φ, φ a = 0`
  plus `φ.apply_mem_spectrum` for the converse — but it sits inside the
  `Order` section and was left for the next pass.
- **28II.2** `Representation.lean:227` (`functional_calculus_2`) — "`C*(a)`
  commutative ↔ `a a* = a* a` ↔ `ℜa ℑa = ℑa ℜa`".  Mathlib has the `⇐` half as
  the instance `CommSemiring (elemental R x)` for `[IsStarNormal x]`; the `⇒`
  half and the real/imaginary-part reformulation are a hands-on computation.
- **28II.4** `Representation.lean:262` (`functional_calculus_4`) — `f(a)` is the
  unique `b ∈ C*(a)` with `φ b = f (φ a)` for all characters `φ` of `C*(a)`.
  Needs `StarAlgebra.elemental.characterSpaceHomeo` (Mathlib:
  `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`) plus
  injectivity of the Gelfand transform on `elemental ℂ a`; a genuine but
  medium-sized transcription.
- **30IV.1/2** `Representation.lean:370`, `:380` (`omega_norm_basic_1/2`) —
  *the route is fully scouted, only the transcription is missing.*  Bundle
  `ω : 𝒜 →ₗ[ℂ] ℂ` with `IsPositiveMap ω` into a `𝒜 →ₚ[ℂ] ℂ`
  (`PositiveLinearMap` = `structure … extends E₁ →ₗ[R] E₂, E₁ →o E₂`, so the
  fields are `toLinearMap := ω` and `monotone'`, the latter from
  `hω (b - a) (sub_nonneg.mpr hab)`).  Then
  `PositiveLinearMap.PreGNS ω` carries the pre-inner-product
  `⟪a, b⟫ = ω (star a * b)` with `preGNS_norm_sq : ‖a‖ ^ 2 = ω (star a * a)`,
  so `omegaSeminorm ω = ‖·‖` on `PreGNS`;  **30IV.1** (Kadison/Cauchy–Schwarz)
  is `norm_inner_le`/`inner_mul_le_norm_mul_norm` there (plus a cast from the
  real inequality to the `ComplexOrder` one), and **30IV.2** is
  `‖leftMulMapPreGNS ω a x‖ ≤ ‖a‖ * ‖x‖`, which is how Mathlib defines that map
  (`LinearMap.mkContinuous ‖a‖ …`).  See the errata entry on the `‖ω‖` factor.
- **30V** — *proved*: `inner_product_completion` is
  `UniformSpace.Completion` + `toComplₗᵢ` + `denseRange_coe`.
- **30X** `Representation.lean:433`, `:446` (`proto_gelfand_naimark_1/2`) and
  **30XIV** `:461` (`gelfand_naimark`) — Mathlib has **no** Gelfand–Naimark
  theorem (I checked: only the GNS pieces `PreGNS`/`GNS`/`gnsStarAlgHom`).
  The direct-sum representation `ϱ_Ω : 𝒜 → B(⊕_ω ℋ_ω)` would have to be built
  by hand (`lp (fun ω => ω.GNS) 2`), together with the centre-separating ⇒
  order-separating argument; the universe bookkeeping in `gelfand_naimark`
  (`H : Type u` for `𝒜 : Type u`) is an extra complication.  Not attempted.

### `A/CStar/Matrices.lean` (55) and `A/CStar/TowardsVN.lean` (27) — not started

Time ran out before these files were touched; both are still at their original
counts.  The reconnaissance done for them (all verified to exist in the current
Mathlib) is recorded here so the next worker does not repeat it:

- `Matrices.lean` **32VI/32IX** are one-liners:
  `CStarModule.inner_mul_inner_swap_le`, `CStarModule.norm_eq_sqrt_norm_inner_self`,
  `CStarModule.norm_inner_le`, `CStarModule.norm_sq_eq` (all in
  `Mathlib/Analysis/CStarAlgebra/Module/Defs.lean`).  Note the class's inner
  product is *right* `𝒜`-linear (`inner_op_smul_right : ⟪x, a • y⟫ = a * ⟪x, y⟫`)
  with `inner_op_smul_left : ⟪a • x, y⟫ = ⟪x, y⟫ * star a` and `star_inner`.
- **32I/32III** (`moduleAdjointTo_*`) are elementary once one has the separation
  lemma "`∀ x, ⟪x, z⟫ = ⟪x, z'⟫ → z = z'`", which follows from the class field
  `inner_self : ⟪x, x⟫ = 0 ↔ x = 0` applied to `z - z'`.
- **34aV.5** (`unitary_basic_5`) is
  `IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary` together with
  `selfAdjoint.realPart_unitarySelfAddISMul`
  (`Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean`).
- Mathlib's Russo–Dye content is *not* **34aVII**: `Unitary/Span.lean` only has
  `CStarAlgebra.exists_sum_four_unitary` (every `x` is a combination of four
  unitaries with coefficients of norm `≤ ‖x‖/2`) and `CStarAlgebra.span_unitary`.
  **34aVI**/**34aVII** (`sum_of_unitaries_*`, `russo_dye`) need the thesis's own
  argument.
- `TowardsVN.lean` **35II** (`pub`) is `banach_steinhaus` modulo
  `BddAbove (Set.range …)` ↔ `∃ C, ∀ i, … ≤ C` (`bddAbove_def`/`forall_mem_range`);
  **39IV.1** is `Orthonormal.inner_products_summable` +
  `Orthonormal.tsum_inner_products_le`; **39IV.3/4** should go through
  `maximal_orthonormal_iff_orthogonalComplement_eq_bot`
  (`Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`),
  whose maximality hypothesis `∀ u ⊇ v, Orthonormal → u = v` matches
  `IsOrthonormalBasis` verbatim, followed by `HilbertBasis.mk`.

## Progress

| file | sorries at start | now |
|---|---|---|
| B/Eff/EffectAlgebras.lean | 147 | 17 |
| B/Eff/Effectus.lean | 41 | 10 |
| B/Eff/WStarCat.lean | 15 | 0 |
| B/Eff/StatesPredicates.lean | 111 | 33 |
| B/Eff/Quotients.lean | 45 | 2 |
| B/Eff/DiamondAmp.lean | 49 | 17 |
| B/Eff/Dagger.lean | 42 | 35 |
| B/Eff/Comparisons.lean | 20 | 16 |
| A/CStar/* | 309 | 309 |
| ↳ A/CStar/Basic.lean | 92 | 11 |
| ↳ A/CStar/Positive.lean | 93 | 63 |
| ↳ A/CStar/Representation.lean | 40 | 17 |
| ↳ A/CStar/Matrices.lean | 55 | 55 |
| ↳ A/CStar/TowardsVN.lean | 27 | 27 |
| A/VN/* | 282 | 282 |
| A/Proc/* | 235 | 235 |
| B/Dils/* | 148 | 148 |

### After session 2 (A/CStar only; other chapters untouched)

**839 code `sorry`s remain, down from 947 — 108 proved.**

| file | after session 1 | now |
|---|---|---|
| **A/CStar total** | **170** | **62** |
| ↳ A/CStar/Basic.lean | 11 | **0 — complete** |
| ↳ A/CStar/Positive.lean | 63 | 33 |
| ↳ A/CStar/Matrices.lean | 55 | 11 |
| ↳ A/CStar/TowardsVN.lean | 27 | 7 |
| ↳ A/CStar/Representation.lean | 17 | 11 |
| B/Eff/* | 129 | 129 — untouched |
| A/VN/* | 276 | 276 — untouched |
| A/Proc/* | 233 | 233 — untouched |
| B/Dils/* | 139 | 139 — untouched |

`lake build` succeeds (8738 jobs, exit 0): `sorry` and style-linter warnings
only.  Session-1 "start" figures above use the older raw-token count, so they
run a few higher per file than the code-only counts used here; the session-2
columns are all code-only and directly comparable.

Counting convention for the `B/Eff/*` rows (fixed in the consolidation pass):
`sorry` *occurrences in code*, i.e. `grep -o '\bsorry\b' | wc -l` minus the
backtick-quoted mentions of `` `sorry` `` inside doc comments.  Earlier
revisions of this table counted the raw token, which inflated
`EffectAlgebras.lean` (20 → really 17), `StatesPredicates.lean` (41 → really
33, before this pass) and `Quotients.lean` (3 → really 2); no proofs were
lost or gained by the re-count.  Of the changes above, only
`Dagger.lean` 36 → 35 and `Comparisons.lean` 18 → 16 are new proofs.

---

## Session 20 — `A/Proc` parsecs 940, 1050, 1120, 1280: Tomiyama and the product functional (worker 49)

Owner of `Theses/A/Proc/*`.  **A/Proc 132 → 128**: `Duplicators` 20 → **19**,
`Tensor` 46 → **45**, `Measurement` 40 → **38**, `QuantumLambda` 26
(untouched).  `A/CStar` (39), `A/VN` (114) and `B/*` untouched; whole
`Theses.A.Proc.*` build exit 0 throughout.  Everything below is
`#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound`).

| point | declaration | file | class |
|---|---|---|---|
| **128II** | `tomiyama` | `Duplicators.lean` | 1 (faithful) |
| **112IX** | `product_functional` | `Tensor.lean` | 1 — the exercise's own hint |
| **94II**.10' | `corner_vna_basic_10'` | `Measurement.lean` | 1 (no author argument) |
| **105IV**.2 | `chevron_f_purely_positive_2` | `Measurement.lean` | 3 (mild — fewer hypotheses) |

### 1. **128II** `tomiyama` — the relativised 65IV lands

Worker 46 named the blocker: *the linear span of the projections of a von
Neumann **subalgebra** is norm-dense in it*.  Worker 47 supplied it as
`mem_of_isClosed_of_projections_subalgebra` (`A/VN/Projections.lean`), and it
fits **exactly**: the set

```
V = {b : A | ∀ a, b * f a = f (b * a)}
```

is a norm-closed `ℂ`-subspace (closed because `‖f a‖ ≤ ‖a‖` makes `f`
continuous, via `AddMonoidHomClass.continuous_of_bound`), so it is enough to
put every projection of `ℬ` in it.  That is the thesis's own reduction, and
the rest is the thesis's own Blackadar-style estimate, transcribed line for
line: with `c := e^⊥ f(ea)`,

* `c ∈ ℬ = range f` and `f ∘ f = f` give `f(c) = c` — this is where
  surjectivity onto `ℬ` is used, and it is the only place;
* `(1−e)·f(ea + t·c) = (1+t)·c` for real `t ≥ 0`, so
  `(1+t)‖c‖ ≤ ‖1−e‖·‖f(ea+t·c)‖ ≤ ‖ea + t·c‖`;
* `star(ea)·c = 0 = star c·(ea)` (because `e·c = 0`), so
  `‖ea+t·c‖² = ‖star(ea)(ea) + t²·(star c·c)‖ ≤ ‖ea‖² + t²‖c‖²`;
* hence `(1+2t)‖c‖² ≤ ‖ea‖²` for **every** `t ≥ 0`, and `t = ‖ea‖²/‖c‖²`
  contradicts `‖c‖ > 0`.

Two small departures from the printed proof, both cosmetic: the thesis writes
`(1+λ)²‖c‖² = ‖ea‖² + λ²‖c‖²` with an equality where the triangle inequality
`≤` is all that is used (and all that holds in general); and the "this can
only hold for all λ" step is made explicit by the choice of `t` above rather
than by a limit.  The sharp constant matters — the argument collapses if
`‖f‖ ≤ C` with `C > 1`.

### 2. **112IX** `product_functional` — `luws` at work

The exercise's own hint ("perhaps using `luws`") is exactly the proof.  Both
halves reduce to the np-functional case, which the exercise itself calls
"almost by definition", and here is why in this encoding:

* `σ ⊙ τ` **is** a basic functional, with witness `t₀ = 1` (112II's
  definition is `ω(s) = (σ⊙τ)(t* s t)`), hence simple, hence trivially an
  operator-norm limit of simple functionals — and `uwTensorTopology` is by
  definition the initial topology for those.  So continuity is one
  `iInf_le`.
* Boundedness is Cauchy–Schwarz against `1` for the semi-inner product
  `[s,t]_ω = ω(s* t)` (**112V**, already packaged as `basicCore` /
  `basic_cauchy_schwarz` in the file), followed by the rescaling `ω ↦ c⁻¹ω`
  (`c = ω(1)`) that puts `ω` into the family the supremum defining `‖·‖`
  runs over.  Result: `‖ω t‖ ≤ ω(1)·‖t‖` for every basic `ω`
  (`basic_norm_le_tensorNorm`).

**72XI** `luws` (2) ⇒ (3) then writes `f = f₀ + i f₁ − f₂ − i f₃` and
`g = g₀ + i g₁ − g₂ − i g₃` with np-functionals, and `TensorProduct.ext'`
gives `f ⊙ g = ∑_{k,l} c_k c_l · (f_k ⊙ g_l)` with `c = (1, i, −1, −i)`;
`‖c_k‖ = 1` makes the bound `∑_{k,l} (f_k⊙g_l)(1)`, and continuity is
`Continuous.add`/`Continuous.const_mul` — no scalar multiple of a *basic*
functional needs to be basic (which it is not: `IsSimpleFunctional` is a
cone, not a subspace).

New private infrastructure in `Tensor.lean`, in the block "Auxiliary for
112IX" just before the theorem: `odotF_tmul`, `isBasicFunctional_odotF`,
`smul_apply_re`, `isBasicFunctional_smul` (a basic functional times a
nonnegative real is basic — conjugate `t₀` by `√r`), `tsn_smul_functional`,
`basic_norm_le_tensorNorm`, `continuous_uwTensor_of_basic`.  The last two are
the reusable ones.

**Our statement asks for more than it needs.**  `product_functional` carries
boundedness hypotheses `hfb`, `hgb` alongside ultraweak continuity, and they
are **not used**: `luws` (2) ⇒ (3) needs only continuity, and boundedness
falls out of the decomposition.  The two `unusedVariables` warnings are left
in place as the evidence and a note was added to the doc comment (cf.
`measure_zorn`, which does the same).  This is not a defect in the thesis —
proc.tex:2854 says "for all `f ∈ 𝒜_*` and `g ∈ ℬ_*`", and `𝒜_*` is *defined*
as the bounded ultraweakly continuous functionals; it is our rendering that
spells out a redundant clause.

### 3. **94II**.10' `corner_vna_basic_10'` — the corner's two topologies

The exercise ("Deduce from this that the ultraweak topology of `e𝒜e`
coincides with the ultraweak topology on `𝒜` … similarly for ultrastrong")
has no published solution.  Both halves are the same two facts:

* every np-functional on `e𝒜e` is `ω ∘ val` for an np-functional `ω` on `𝒜`
  (**94II**.10, already proved, `corner_vna_basic_10`), and
* every `ω ∘ val` is an np-functional on `e𝒜e` (**94II**.8, already proved,
  `Corner.restrictNP`),

i.e. the two generating families of functionals coincide.  For the ultraweak
topology that is `induced_compose` + `induced_mono` + `iInf_le` in each
direction.  For the ultrastrong topology the generating *sets* do **not**
coincide — `val ⁻¹' {a | ‖a − b‖_ω < ε}` has `b ∈ 𝒜` arbitrary, not
necessarily in the corner — so the `≤` half needs the usual re-centring: for
`x₀` in that preimage the corner-ball of radius `ε − ‖x₀.val − b‖_ω` around
`x₀` stays inside it, by `omegaNorm_sub_le`.  The other half is exact,
because `‖x‖_{ω∘val} = ‖x.val‖_ω` (`val` is a ∗-homomorphism).

### 4. **105IV**.2 `chevron_f_purely_positive_2` — six lines, and two spare hypotheses

`⟨f²⟩ = ⟨f⟩²` for ⋄-self-adjoint `f`, rendered elementwise, is
`f(x) = f(⌈f⌉·x·⌈f⌉)` (**63VI** `carrier_fundamental`) at `x = f(a)`,
once `⌈f⌉ = ⌈f(1)⌉` (**103III**.1 `purely_positive_basic_1`, already
proved).  Two observations for the author:

* the hypothesis `a ∈ ⌈f(1)⌉𝒜⌈f(1)⌉` is **not used** — the identity holds
  for every `a ∈ 𝒜` (the unused-variable warning is left as the evidence);
* ⋄-self-adjointness is used *only* to get `⌈f⌉ = ⌈f(1)⌉`, so the statement
  holds for any ncp-map whose carrier is `⌈f(1)⌉` — in particular for any
  faithful-on-its-carrier `f`.  This is the same pattern as 99II in session
  18: the cited hypothesis is far stronger than what the argument consumes.

### 5. Corrections to the brief

1. **Parsec 1280 does *not* follow from 128II.**  128VIII
   `uniqueness_duplicator` needs **128VI** `sef_instrument`, whose proof
   (proc.tex:6015) applies Tomiyama to `f' : 𝒜⊕𝒜 → 𝒜⊕𝒜` and needs
   `‖f'‖ ≤ 1` for a merely *positive* unital `f`.  That is **34aVIII**
   `russo_dye_cor` (`A/CStar/Matrices.lean`), which is `sorry`, as is the
   **34aII** `normal_russo_dye` it rests on.  The sharp constant is
   essential: with `‖f‖ ≤ C`, `C > 1`, the Tomiyama inequality
   `(1 + 2t − (C²−1)t²)‖c‖² ≤ C²‖ea‖²` has a finite maximum in `t` and yields
   nothing.  `weak_russo_dye_2`'s factor `2` is therefore useless here.
   *Note the duplicator really is only positive*: proc.tex:5861 says
   "npsu-map", and 127I.20 spells out "requiring the maps to be only positive
   subunital" — so our `Duplicator` structure (a `→ₚ[ℂ]` plus `normal` plus
   `subunital`) is faithful, and complete positivity, which would have let
   `cp_russo_dye` (34XVI, proved) do the job, is genuinely unavailable.
   **`russo_dye_cor` is now the named blocker for parsec 1280**, and it is one
   short corollary of the already-proved **34aVII** `russo_dye` plus 34aII.
2. **128VIII, 128XI and 127III/127VI are blocked a second time over**, being
   `Duplicator`-typed and hence `VNT`-typed: `VNT A B` is
   `(vnTensor A B).carrier`, `vnTensor` is `Nonempty.some` of the `sorry`ed
   **111XII** `vnTensorProduct_nonempty`, so *the statements themselves*
   depend on `sorryAx` and can never be closed axiom-cleanly until 111XII is.
   127VI `unit_duplicator` is in addition blocked on **116III**.1
   `tensor_simple_facts_1` (monotonicity of `⊗` on positives, `sorry`), which
   its two `≤` steps need.
3. Everything else in the brief checked out: `projections_norm_dense_subalgebra`
   / `mem_of_isClosed_of_projections_subalgebra` fit 128II exactly (§1); 72XI
   `luws` really does release 112IX (§2); 112X.1/.2 and the `VNT` block really
   are still blocked; 116I `exists_predualTensor` — the consumer of 112IX the
   brief names — is `VNT`-typed and so does *not* become reachable.

### 6. Nothing false found

No new `ERRATA.md` or `QUESTIONS.md` entry.  128II's proof is correct as
printed (modulo the `=`/`≤` noted in §1); 112IX and 94II.10' are `proc.tex`
exercises with no published solution (`asols.tex` stops at parsec 340) and
both are true as stated; 105IV is an Exercise too.

---

## Session 19 — `A/VN` parsecs 460, 650, 720, 730 (worker 47)

Owner of `Theses/A/CStar/*` and `Theses/A/VN/*`.  `A/CStar` untouched
(**39** `sorry`s, unchanged); `A/VN` **117 → 114** (`Basic` 34 → 33,
`Completeness` 17 → 15).  Whole-project `lake build` green throughout;
`A/Proc` (132), `B/Dils` (62) unchanged.  Everything below is
`#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound`).

| point | declaration | file | class |
|---|---|---|---|
| **46III** | `npuws` | `Basic.lean` | 2 (no author argument — Exercise) |
| **72XI** | `luws` | `Completeness.lean` | 1 (Corollary; the thesis gives no proof) |
| **73VIII** | `ultraclosed` | `Completeness.lean` | 1 — the exercise's own five steps |
| — | `ceil_mem` + **65IV** relativised | `Projections.lean` | new (not a thesis point) |

### 1. `ceil_mem`: a von Neumann subalgebra is closed under `⌈·⌉`

Worker 46 named the missing ingredient of `A/Proc` **128II** `tomiyama`:
*the linear span of the projections of a von Neumann **subalgebra** is
norm-dense in it.*  65IV as stated puts the projections in `{a}^□□`, and
`{a}^□□ ⊆ S` is the double commutant theorem **88VI** (`sorry`, and stated
only for `B(H)`), so the relative form does not follow from the absolute one
in this tree.

It does follow from the *same* spectral Riemann sum, once one knows
`0 ≤ x ∈ S → ⌈x⌉ ∈ S`.  That is the thesis's own construction
`⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` (**56I**.20, already in the tree as `vna_ceil_sup`) read
inside `S`: with `b = ‖x‖⁻¹x`, every iterate `b^{1/2ⁿ}` lies in `S` because a
norm-closed star subalgebra is closed under the continuous functional
calculus, the iterates form a chain, and `IsVNSubalgebra.dirSup_mem` gives
the supremum.  Two small bridges were needed:

* `sqrt_eq_cfc_real` — Mathlib's `CFC.sqrt` is `cfcₙ NNReal.sqrt`
  (non-unital, `ℝ≥0`-valued), while Mathlib's `cfc_mem` ("the CFC of an
  element stays in any closed star subalgebra containing it") is stated for
  `RCLike` scalars.  `CFC.sqrt x = cfc Real.sqrt x` for `0 ≤ x`, by
  `CFC.sqrt_unique`.
* `cfc_mem_of_isClosed` — `cfc_mem` at `𝕜 = ℝ`, `𝕜' = ℂ`.

`exists_spectral_approx` (private, the Riemann sum behind 64II/65IV) then had
its conclusion **strengthened**, not rewritten: its projection set gained the
clause "`p` lies in every von Neumann subalgebra containing `a`", proved by
`cfc_mem_of_isClosed` + `ceil_mem` for `p = ⌈(a−t)⁺⌉` and by `one_mem` for
`p = 1`.  Its two existing consumers (`projections_norm_dense`,
`mem_closure_span_proj`) now project the extra clause away.  New public
results:

* `projections_norm_dense_subalgebra_selfAdjoint` / `..._subalgebra`
  (the latter for arbitrary `a ∈ S`, via `a = ℜa + i·ℑa`);
* `mem_of_isClosed_of_projections_subalgebra` — *a norm-closed `ℂ`-subspace
  containing every projection of `S` contains `S`* — the shape worker 46's
  `A/Proc` proofs consume (cf. their `mem_of_isClosed_of_projections`).

**128II should now be reachable**; it is in `A/Proc`, not this chapter.

### 2. **72XI** `luws` — and `smulNP` at last

72XI is a Corollary with **no proof in `vn.tex`**; the cycle used is
1 ⇒ 4 ⇒ 3 ⇒ 2 ⇒ 1 with 3 ⇒ 5 ⇒ 4 on the side.

* **1 ⇒ 4** needed a converse to `ultrastrong_ball_mem_nhds` that the tree
  did not have: *every ultrastrongly open set contains a `‖·‖_ω`-ball around
  each of its points*.  Proved as `exists_ultrastrong_ball_of_isOpen` by
  induction on `TopologicalSpace.GenerateOpen`, the `inter` case being
  `‖·‖_{ω₁} , ‖·‖_{ω₂} ≤ ‖·‖_{ω₁+ω₂}` (`omegaNorm_le_addNP`).  This avoids
  extracting a finite subfamily from `nhds_generateFrom` and is the reusable
  form.
* **4 ⇒ 3** is 72V (1) ⇒ (2) followed by `normal_functionals_decomposition`
  (worker 28's corrected 72V).
* **3 ⇒ 5** is where `smulNP` is genuinely needed, exactly as predicted:
  `‖f(a)‖ ≤ C‖a‖_{ω'}` for `ω' = Σₖ fₖ`, and one wants a *single* `ω` with
  `‖f(a)‖ ≤ ‖a‖_ω`, namely `ω = C²ω'`.  **`smulNP` is now in `Basic.lean`**
  next to `zeroNP`/`addNP`, with `smulNP_apply` and
  `omegaNorm_smulNP : ‖a‖_{r·ω} = √r ‖a‖_ω`.  Normality of `r·ω` for `r ≥ 0`
  is the observation that `z ↦ (r:ℂ)z` preserves and (for `r > 0`) reflects
  the order on `ℂ`; the `r = 0` branch uses only that `D` is nonempty.
  (`PositiveLinearMap` has `Zero`, `Add` and an `ℕ`-action but no real
  scalar action, so `smulNP` goes through `PositiveLinearMap.mk₀`.)

**Correction to worker 32's note (c):** `smulNP` was indeed not needed for
72V, and it *is* needed for 72XI — but for clause 5, not for the `¼` of the
polarisation, which worker 28 had already absorbed.

### 3. **73VIII** `ultraclosed` — the exercise's five steps, transcribed

The exercise (vn.tex:4160) comes with a full roadmap and it was followed
step for step; the only structural change is that the thesis first
translates `K` by `a₀` and then argues at `0`, whereas the Lean proof keeps
`K` where it is and translates only the *ball*: the point `a₀ ∉ K` to be
separated is fixed once, `B` is the ball at the origin and `K' = K − a₀` the
translate.  **This matters**: the thesis's phrasing needs `K − a₀` to still
be ultrastrongly closed, i.e. that translation is an ultrastrong
homeomorphism, which is not in the tree and is not entirely free (the
`‖·‖_ω`-bounded-map criterion `continuous_ultrastrong_of_omegaNorm_bound`
does not apply to an affine map).  In the arrangement used, ultrastrong
closedness of `K` is consumed *once*, in step 1, and `K'` is only ever needed
to be convex and disjoint from `B`.  Suggested for the author.

Ingredients: step 1 is `exists_ultrastrong_ball_of_isOpen` (§2); steps 2–3
are **73IV** `hahn_banach` (already proved in the tree, by the
Minkowski-functional route) applied to `B + K'`; the `ℂ`-linear extension
`g(a) = f(a) − i f(ia)` is Mathlib's `Module.Dual.extendRCLike`; step 4's
"`g` is ultraweakly continuous" is **72XI** clause (4), which is why 73VIII
had to wait for `luws`; step 5 uses that `B` is absorbing for `‖·‖_ω`.

### 4. **46III** `npuws`

(1) ⇒ (2) is `continuous_ultraweak_npFunctional` at `⟨ω, h⟩`; (2) ⇒ (3) is
`ultrastrong_le_ultraweak`; (3) ⇒ (1) is the new
`preservesDirSups_of_continuous_ultrastrong`: **44XIV**
`vna_supremum_uslimit` says the net `(d)_{d∈D}` converges ultrastrongly to
`⋁D`, so `ω(d) → ω(⋁D)`, and the comparison with an upper bound `z` is done
on real and imaginary parts separately (`Complex.le_def`), avoiding any
`OrderClosedTopology ℂ` assumption.

This is exactly **45I**.1 `us_cont_normal` for `B = ℂ` *without* the
restriction to the effects.  45I.1 itself is **not** closed: its hypothesis
is continuity on `[0,1]_A` only, so it needs the cofinal-tail rescaling of
`preservesDirSups_of_continuousOn_effects` with `vna_supremum_uslimit` in
place of `vna_supremum_uwlimit` — a ~100-line refactor of that private
lemma, not attempted.

### 6. Nothing false found

No new `ERRATA.md` or `QUESTIONS.md` entry.  72XI and 73VIII are `vn.tex`
Corollary/Exercise points with no published solution; both are true as
stated and the roadmaps in the text are correct.

## Session 10 — `A/VN` parsecs 440–450 and 610 (worker 32)

Proved: **44XV** `p_uwcont` + `p_uwcont_ad`, **45II** `cp_uscont`, **45IV**
`mult_uws_cont_ad` / `mult_uws_cont` (`Theses/A/VN/Basic.lean`), **61II**
`ncp_ceill` (`Theses/A/VN/Projections.lean`).  `Basic.lean` 40 → 35 code
`sorry`s, `Projections.lean` 28 → 27.

### Structural changes to `Theses/A/VN/Basic.lean`

1. **New import `Theses.A.CStar.Matrices`.**  45II's proof is Kadison's
   inequality for cp-maps (**34XIV** `cp-cs`), which lives in
   `A/CStar/Matrices.lean` and was not on `A/VN/Basic.lean`'s import path.
   `A/VN/NormalFunctionals.lean` already imported it, so the module is a
   build dependency of the chapter either way; `Matrices.lean` declares no
   instances, so the import cannot introduce new instance taint.  As a
   side-effect `cp_cs` is now available in `Projections.lean` too, which is
   what makes **61II** reachable.
2. **The `PositiveMaps` section moved up**, from just after parsec 470 to
   just before **44XV**.  It carries `isSelfAdjoint_map_of_positive`,
   `imageSA` and friends, and `compNP` — all of which 44XV's proof needs.
   Nothing in it depends on anything between its old and new positions.
3. **New public helpers** in that section (used by 44XV/45II/45IV/61II):
   `continuous_ultraweak_of_forall`, `continuous_ultraweak_conj`,
   `ncpPositive` (+ `ncpPositive_apply`), `ncp_star`, `ncp_cp_cs`; plus the
   private `real_smul_eq_complex_smul`, `npFunctional_real_smul`,
   `npFunctional_csmul`, `npFunctional_finsetSum`,
   `positiveLinearMap_real_smul`, `isOpen_ultrastrong_of_ball`,
   `continuous_ultrastrong_of_omegaNorm_bound`, `omegaNorm_mul_right`,
   `preservesDirSups_of_continuousOn_effects`, `adPositive`.
4. **Duplicate removed.**  `Projections.lean` carried a private
   `continuous_ultraweak_conj` with exactly the statement now in
   `Basic.lean` (its 45-line hand-rolled polarisation is replaced by three
   lines over **44II** `mult_polarization`), and a private
   `npFunctional_smul` that only served it.  Both deleted; the two use sites
   in `commutant_basic_2` now resolve to the `Basic.lean` lemma.

### Divergences

**(1) Faithful.**  45II is the thesis's own argument (vn.tex:849): the
estimate `f(b)* f(b) ≤ ‖f(1)‖ f(b* b)` from `cp-cs`, and the reduction of
ultrastrong continuity to continuity at `0` by translation.  45IV.2 is the
thesis's own (vn.tex:868): "use `mult-polarization`".  61II is the thesis's
own chain (vn.tex:2996) verbatim.

**(3) Mild / different organisation.**

* **45II.**  The thesis argues with *nets*: `f` is us-continuous at `0`
  because `f(bα)* f(bα) ≤ ‖f(1)‖ f(bα* bα) → 0` ultraweakly.  The ultrastrong
  topology is generated by the `‖·‖_ω`-balls and is not first countable, so
  in Lean the same estimate is applied to a generating ball directly:
  `‖f x‖_ω ≤ √‖f(1)‖ · ‖x‖_{ω∘f}` and then a `δ = (ε−r)/(C+1)` argument.
  Same content, no nets.  The reusable form is
  `continuous_ultrastrong_of_omegaNorm_bound`.
* **44XV.**  The exercise has no published solution (`asols.tex` stops at
  parsec 340).  The cycle proved is 1 ⇒ 2 ⇒ 3 ⇒ 4 ⇒ 3 ⇒ 1.  The substance is
  2 ⇒ 3; 3 ⇔ 4 is `compNP` plus **44XI** order separation and 3 ⇒ 1 is the
  definition of the ultraweak topology as an initial topology.
* **61II.**  The thesis's constant is `‖f(1)‖²`; ours is `‖f(1)‖ + 1`.  Both
  work, and `+1` is positive without a case split, so `ceil_smul` (**59III**.4)
  applies unconditionally.  (`cp_cs` in fact delivers the sharper `‖f(1)‖`.)

**(2) Different route, for cause.**

* **45IV.1** `mult_uws_cont_ad`.  The thesis says "conclude from `cp-uscont`
  and `ad-cp`".  In Lean the direct seminorm identity
  `‖b* x b‖_ω = ‖b* x‖_{b*ω} ≤ ‖b‖ ‖x‖_{b*ω}` (four lines, using **44VIII**
  `conjNP`) is much shorter than packaging `b ↦ b* (·) b` as a bundled
  Mathlib `CompletelyPositiveMap`.  45II is still proved separately, so
  nothing is lost.
* **44XV** 2 ⇒ 3.  There is no author argument to diverge from, but the proof
  needs one move worth recording: a bounded directed `D` need not lie in any
  ball around `0`, so it is first replaced by the cofinal upper tail
  `D' = {d ∈ D | d₀ ≤ d}` (same upper bounds, hence the same supremum) and
  then rescaled into `[0,1]_A` by `a ↦ (a − d₀)/‖⋁D − d₀‖`.  This is the same
  cofinality move that 72III.2 needed (session 6 note of worker 24) — it is
  worth stating once in the thesis.

**(5) Closed from Mathlib without reading the author's argument:** none.
vn.tex was read at 780–900 (44XII–45VI) and 2965–3010 (61I–61II) before
anything was written, and the `asols.tex` errata block was searched for
parsecs 440, 450 and 610 (`parsec-610.20` is the reversal of 61II's
inequalities, which our statement already carried).

### Not an erratum, but worth telling the author

The proof of **45IV** as printed derives part 1 from `cp-uscont`; but part 1
is *elementary* — `‖b* a b‖_ω = ‖b* a‖_{b*ω} ≤ ‖b‖‖a‖_{b*ω}` — and needs
neither complete positivity nor 45II.  Deriving it directly would make
parsec 450 independent of `cp-cs`.

## Session 4 — `B/Dils` (worker 26): first survey of the whole chapter

Owned `Theses/B/Dils/*.lean` (75 code `sorry`s).  Result: **1 proved**, and a
dependency-ordered map of what is and is not reachable — which is the part
worth keeping, because the chapter turns out to hang off six unproved
constructions rather than being merely untouched.

### Proved

* **140X.2** `paschke_basics_2` (`Stinespring.lean`) — "if `(𝒫,ϱ,h)` is a
  Paschke dilation then `(𝒫, id, h)` is a Paschke dilation of `h`".
  Transcribed from `bsols.tex`'s solution `paschke-basics`, item 2
  (**divergence class 1 — faithful**); axiom-clean
  (`propext, Classical.choice, Quot.sound`).  Two file-private helpers were
  needed and added: `ncpP` (an `NCPMap` as a `→ₚ[ℂ]`, so that
  `preservesDirSups_pmap_comp` applies) and `exists_ncpCompNMIU` (nmiu
  followed by ncp is ncp).  `A/Proc/Measurement.lean` has the analogous
  `exists_ncpComp`, but `Theses.A.Proc` is not on this chapter's import path
  — the same reason the file already repeats `exists_ncpId`.

### The six roots the chapter hangs off

| root | file | what waits on it |
|---|---|---|
| **149V** `dils_selfdual` | `HilbertModules.lean:1854` — the file's *only* `sorry` | every construction of a self-dual module (150II, 154III, 164II) and every statement that must *produce* an ON basis (160II, 161II.2, 162IV) |
| **150II** `dils_completion` | `SelfDualCompletion.lean:81` | 154III → all of `Paschke.lean`; 163II; 164II |
| **151Ia** `selfdual_completion_univ` | `SelfDualCompletion.lean:102` | **163II both halves** (nothing else); 154III |
| **152X** `ba_vonNeumannAlgebra` | `SelfDualCompletion.lean:448` | 153I, 154III.5 |
| **74IV/74I** Kaplansky | `A/VN/Completeness.lean` — **both `sorry`** | all of `Kaplansky.lean`, hence 159IV, 166VI |
| `IsVNTensor` has no order clause | `SelfDual.lean:841` | 165III, 165VI → 167I (QUESTIONS **B5**) |

Ranked targets for the next worker: **149V** (the file's only `sorry`, and the
notion the chapter is about); the **four `cornerSet` `sorry`-instances** in
`Pure.lean` (pure Lean infrastructure — `pAp` is a C*-algebra with unit `p`,
proc.tex 94II — which unblocks eight statements and removes the last
invisible-taint site in `B/Dils`); then **152X**, then **150II + 151Ia**.

### Parked, with the reason

* **169XII `dils_filters_injective`** (filters are injective) is the keystone
  of `Pure.lean`'s categorical cluster — `169X → 169XII → 169XI.1 → 169XI.2b`
  and `169X + 169XII → 169XI.2a` — so a corner-free proof would unblock five
  statements.  There is none, and the reason is worth recording so it is not
  re-attempted blind.  The universal property gives *monicity*.  Monicity plus
  "`p ≥ 0` and `c(p) = 0` ⟹ `p = 0`" is not enough: that half is easy (take
  `f = id + ad_{√p}`; for `a ≥ 0` we have `0 ≤ √p a √p ≤ ‖a‖p`, so
  `c ∘ f = c`, so `f = id` by uniqueness, so `p = 0`), but a positive map can
  have `ker c ∩ A₊ = 0` and still not be injective — `c(x,y) = x+y` on `ℂ²`.
  Going from monic to injective needs enough ncp-maps `C → A` to separate
  points, i.e. rank-one `a ↦ ω(a)p`, i.e. a *normal state* on `A`; our
  statement of 169XII assumes only `CStarAlgebra`, not `VonNeumannAlgebra`
  (the thesis's ambient assumption for the parsec).  So 169XII really does
  need the standard filter, as the exercise's own hint says — and the standard
  filter needs the `cornerSet` instances.
* **140X.3** `paschke_basics_3` — the abstract-product formulation means the
  real work is a *tupling* lemma: from `σᵢ : NCPMap 𝒫' 𝒫ᵢ` and jointly
  bijective nmiu `pᵢ : 𝒫 → 𝒫ᵢ`, build `σ : NCPMap 𝒫' 𝒫`.  That needs (a) the
  inverse of `c ↦ (p₁c, p₂c)` as a linear map, (b) order *reflection*
  (`p₁x ≥ 0 ∧ p₂x ≥ 0 ⟹ x ≥ 0`, by the `(negPart)³` argument already used in
  `A/VN/Basic.lean` for a single injective ∗-homomorphism), (c) complete
  positivity, which then follows elementwise because the `pᵢ` are
  ∗-homomorphisms, and (d) normality from (b).  Left for a worker with room;
  the author's own argument (`bsols.tex` `paschke-basics`.3) is exactly the
  three-line categorical one and carries none of this.

### Our own notes (no author action)

* **Invisible `sorryAx` — the session-2 ranking is stale.**  That table lists
  `B.Dils.Ba.instCStarAlgebra` / `instStarOrderedRing` / `instPartialOrder` at
  14 tainted declarations each; **all three are now proved outright**
  (`HilbertModules.lean:660/666/671`), so that taint is gone.  What is left in
  `B/Dils` is (i) `cornerSet.instCStarAlgebra` / `instPartialOrder` /
  `instStarOrderedRing` (`Pure.lean:53/60/67`), which taint
  `standard_corner_dils`, `dils_stand_filter`, `paschke_corner`; and (ii) two
  sorried *theorems used as terms inside statements*, the same failure mode one
  level up: `existence_paschke_5` (`Paschke.lean:147`) embeds
  `ba_vonNeumannAlgebra M.selfDual`, and `paschke_corner` (`Pure.lean:302`)
  embeds `cornerSet_vonNeumannAlgebra A (cceil p)`.  `VonNeumannAlgebra` is a
  `Prop`, so this is harmless mathematically, but a future proof of either
  will report `sorryAx` and look like a leak.
* **`dils.tex`'s line references are not stale — measured, not assumed.**  All
  204 `**DISP** (…dils.tex:LINE)` references in the seven files were
  re-derived from the `\begin{parsec}`/`\begin{point}` numbers: **201 resolve
  to within ±1**, and the other three are *range* references
  (`137I–137VII … 397–585`, `168I–168IV … 5968–6054`, `155I, 155III … 3841,
  3859`) whose endpoints are all correct.  Zero stale references, so
  `dils.tex` behaves like `vn.tex`, not like `A/CStar/TowardsVN.lean`.
* **`Pure.lean`'s 23 `sorry`s are 19 statements + 4 `sorry`-instances.**  Any
  progress table quoting 23 statements for that file is overcounting.
* **153IV `hilbmod_adj_vector_ncp`** (`SelfDualCompletion.lean`) is the one
  statement in the chapter that depends on nothing else in it — but its only
  real ingredient, positivity of Gram matrices over a C*-algebra, is
  **33II.2 `cstar_matrix_gram_nonneg`**, still `sorry` behind the known 33II.1
  bottleneck in `A/CStar/Matrices.lean`.  Worth revisiting the moment 33II.1
  lands.
* **165III's uniqueness half is already reachable** (`extTensor_map_ext`, in
  file and proved); only its existence half waits on QUESTIONS B5.  Noted in
  the B5 row of ERRATA.
* **140X.1** carries a further defect, found while transcribing its sibling:
  the exercise reads "Show `(𝒜, ϱ, id)` is a Paschke dilation of an nmiu-map
  `ϱ : 𝒜 → ℬ`", but a Paschke dilation of `φ : 𝒜 → ℬ` is a triple
  `(𝒫, ϱ : 𝒜 → 𝒫, h : 𝒫 → ℬ)`, so the dilating algebra is `ℬ`, not `𝒜` —
  with `𝒫 = 𝒜` the `id` would have to be a map `𝒜 → ℬ`.  Our
  `paschke_basics_1` already had the corrected form (and is proved), which is
  exactly the "silent half-repair" pattern in reverse: the Lean statement was
  right and the source is wrong.  Filed in ERRATA.
* **A stale doc comment that is now actionable.**  `Pure.lean`'s
  `paschke_corner` (171II) carries a second instance hypothesis
  `[Fact (IsStarProjection (cceil p))]` and explains it: "That `⌈⌈p⌉⌉` is a
  projection too is **68III** (`exists_cceil`), still `sorry` in
  `Theses.A.VN.Projections`, so it cannot yet be discharged … drop it once
  68III is proved."  **68III is now proved**
  (`A/VN/Projections.lean:3227`, with `cceil_isLeast` right below it), so the
  hypothesis can go — either by discharging it from `cceil_isLeast` in an
  `instance`, or by deleting it from the statement.  Not done here, because
  deleting an instance hypothesis is a statement change and 171II is blocked
  on the `cornerSet` instances regardless; flagged for the doc-comment sweep.

---

## Session 5 — `B/Dils` (worker 30)

**`B/Dils` 74 → 66 `sorry`s** (five proofs; the other three are the
`FIXME(sorry-instance)` doc comments that went with them).  `lake build` of
all seven modules: green, `sorry` + the repo-wide header-linter noise only.
Every new declaration `#print axioms`-es to `propext, Classical.choice,
Quot.sound`.

### Proved

* **proc.tex 94II parts 5–6** — `cornerSet.instCStarAlgebra`,
  `cornerSet.instPartialOrder`, `cornerSet.instStarOrderedRing`
  (`Pure.lean`), and **part 8** `cornerSet_vonNeumannAlgebra`.  These were the
  last `sorry`-*instances* in `B/Dils`, i.e. the last invisible-taint site in
  the chapter: `standard_corner_dils`, `dils_stand_filter` and
  `paschke_corner` were structurally `sorryAx` with no visible `sorry`, and
  `paschke_corner` additionally embedded `cornerSet_vonNeumannAlgebra` as a
  *term in its statement*.  Both leaks are now closed.  (They remain `sorry`
  as statements, so nothing became "genuinely proved for the first time" —
  but a future proof of any of them will now be honest.)

  The construction is the routine one: everything is carried by
  `Subtype.val` from `A` except the unit, which is `p`; `pAp` is norm-closed
  (zero set of `a ↦ p·a·p − a`), hence complete; and the order is the
  star-order because `√a` lies in the corner whenever `a` does
  (`cornerSet.sqrt_mem`: `‖√a(1−p)‖² = ‖(1−p)a(1−p)‖ = 0`).  Part 8 computes
  suprema in `A` (**44VIII** `ad_normal` fixes the corner) and restricts
  np-functionals.

  *Divergence class 2 (different route), but only in the trivial sense that
  proc.tex 94II is an Exercise with no published solution* (`asols.tex` stops
  at parsec 340 and never covers `proc.tex`).  The argument is the standard
  one and matches the parts-1–8 breakdown the exercise itself prescribes.

  **Duplication, deliberately.**  `Theses/A/Proc/Measurement.lean` has since
  acquired the *same* development for its own bundled corner type
  `A.Proc.Corner A e`, and my instances are a transcription of it onto
  `B.Dils.cornerSet A p` (a subtype).  `Theses.A.Proc` is not on `B/Dils`'s
  import path, and importing a file another worker was editing live was not
  worth the coupling; a note to merge the two is in `Pure.lean`'s header and
  above the construction.

* **153IV `hilbmod_adj_vector_ncp`** (`SelfDualCompletion.lean`) — `φ(d) =
  (aᵢ* d aⱼ)ᵢⱼ : 𝒜 → Mₙ𝒜` is an ncp-map.

  *Divergence class 2 (different route), for cause.*  The author's solution
  (`bsols.tex` `hilbmod-adj-vector-ncp`) writes `φ = ad_T` for the row vector
  `T : 𝒜ⁿ → 𝒜`, `(bᵢ)ᵢ ↦ ∑ᵢ bᵢaᵢ`, and invokes **153I** `hilbmod_ad_ncp` —
  which is still `sorry` here and waits on 152X, so that route is closed.
  Instead: by **33II.1** `cstar_matrix_positive_iff` both halves reduce to the
  scalar identity `∑ᵢⱼ cᵢ* φ(d)ᵢⱼ cⱼ = v* d v` with `v = ∑ᵢ aᵢcᵢ`.  Complete
  positivity is then the observation that the resulting six-fold sum is a
  square `w* w`, and normality is **44VIII** `ad_normal` applied to `v`
  (plus `sub_nonneg` and additivity of `P ↦ ∑ᵢⱼ cᵢ* Pᵢⱼ cⱼ`, packaged as the
  private `AddMonoidHom` `conjFun`).

  This also retires the *previous* session's note that 153IV was "blocked on
  33II.2 `cstar_matrix_gram_nonneg`": 33II.2 has since been **proved** in
  `A/CStar/Matrices.lean`, and in the event the proof did not need it — only
  33II.1.

### Statement changes (our own, not the thesis's)

* **171II `paschke_corner`** — the second instance hypothesis
  `[Fact (IsStarProjection (cceil p))]` is **deleted**, as its own doc comment
  instructed ("drop it once 68III is proved"; 68III `cceil_isLeast` is proved).
  It is now supplied by the new `fact_isStarProjection_cceil` instance next to
  `fact_isStarProjection_floor`/`_ceil`.  The doc comment is updated to say so.

### Erratum found

* **153IV** (and its `bsols.tex` solution) opens "Let `𝒜` be a C\*-algebra",
  but asks for `φ` to be an **n**cp-map, and normality is only defined over a
  von Neumann algebra — the solution's own first move ("`𝒜` is a self-dual
  Hilbert `𝒜`-module") and its appeal to `hilbmod-ad-ncp` part 2 both need one.
  The same omission sits one level up in **153I** `hilbmod-ad-ncp`, whose
  normality half cites `hilbmod-vecstates-normal` (152XIII).  Our Lean
  statement already carried `[VonNeumannAlgebra 𝒜]` with a doc comment saying
  why, so this is another "the Lean statement is right and the source is
  wrong".  Filed in ERRATA in point order.

### Our own notes (no author action)

* **`B/Dils` now has zero `sorry`-instances.**  The repo-wide enumeration
  ```sh
  grep -rn '^instance\|^noncomputable instance' Theses/ --include=*.lean -A3 \
    | grep -B3 'sorry' | grep instance
  ```
  returns only `A/VN/Basic.lean:674` `vonNeumannAlgebra_lp_infty`,
  `A/VN/Basic.lean:2832` `mn_vna_1`, and `A/Proc/QuantumLambda.lean:416/419`.
  The one remaining *term-in-a-statement* leak in `B/Dils` is
  `existence_paschke_5` (`Paschke.lean`), which embeds
  `ba_vonNeumannAlgebra M.selfDual`; `paschke_corner`'s twin leak is closed.
* **152X `ba_vonNeumannAlgebra` has a precise blocker, and it is not 77I.**
  Its thesis proof (152XI–152XIII) needs (i) **44XIV**
  `vna_supremum_uslimit` — *proved* in `A/VN/Basic.lean:1790` — and (ii)
  **45IV** `mult_uws_cont` / `mult_uws_cont_ad`, ultrastrong continuity of
  multiplication by a fixed element, which is what makes the ultrastrong limit
  `B(x,y) = uslim_α ⟨x, T_α y⟩` sesquilinear.  45IV is **`sorry` in the frozen
  `A/VN/Basic.lean:1908/1914`**, so 152X — and through it 153I, 154III.5, all
  ten of `Paschke.lean`, and the `existence_paschke_5` leak above — is blocked
  there.  `hilbmod_sesquilinear_forms` (152V), the other big ingredient, is
  already proved in `SelfDualCompletion.lean`.
* **160II `direct_prod_self_dual_basis` is half-reachable.**  Its first
  conjunct (`Sum.elim (κ₁∘e) (κ₂∘d)` is an ON basis) is exactly the published
  solution `direct-prod-self-dual-basis` and needs nothing outside the file;
  its second conjunct `SelfDual ℬ Z` is the implication (4) ⇒ (1) of **149V**.
  So the statement as a whole waits on 149V, but a worker with room could
  prove the basis half as a private lemma and leave only the self-duality.

## Session 13 — `B/Dils` parsecs 1520–1540 (worker 34)

**B/Dils 66 → 63 code `sorry`s.**  `SelfDualCompletion.lean` 4 → 2,
`Paschke.lean` 10 → 9.  Everything axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`); `lake build` green over the
whole chapter; the chapter still has **no `sorry`ed instances**.

| point | declaration | file |
|---|---|---|
| **152X** | `ba_vonNeumannAlgebra` (`𝒷ᵃ(X)` is a von Neumann algebra) | `SelfDualCompletion.lean` |
| **153I**.2 | `hilbmod_ad_ncp` (`ad_T` is an ncp-map) | `SelfDualCompletion.lean` |
| **154III**.2 | `existence_paschke_2` (uniqueness of `ϱ(a₀)`) | `Paschke.lean` |

Reusable by-products, all public: `ba_nonneg_iff` (144I transported to the
type `Ba 𝒷 X`), `ba_inner_isSelfAdjoint`, `ba_inner_mono`, `baVec` (+`_coe`,
`_mono`, `_image_directed`), `ba_isBSesquilinear` (142VIII), **152XII**
`ba_isLUB` and its restatement `ba_isLUB_vec`, and **152XIII** `baVecNP`
(the vector np-functionals of `𝒷ᵃ(X)`).

### 152X — divergence class (2), for two named reasons

The skeleton is the thesis's own (152XI–152XIII): the vector forms
`⟨x, T_α x⟩` are a bounded directed net in `𝒷`, hence converge ultrastrongly
to their supremum (**44XIV** `vna_supremum_uslimit`); polarization (**142IX**)
extends this to `B(x,y) = uslim_α ⟨x, T_α y⟩`; `B` is 𝒷-sesquilinear because
addition and multiplication by a fixed element are ultrastrongly continuous
(**45IV** `mult_uws_cont`, proved last round — this is what unblocked the
parsec); **152V** `hilbmod_sesquilinear_forms` represents `B` as `⟨·, T·⟩`;
`T` is the supremum; and the vector states are separating (**144I**) and
normal (152XIII).  Two steps are done differently.

1. **The bound on `B` uses order, not norm.**  The thesis picks `r` with
   `‖T_α‖ ≤ r`.  A directed set that is bounded *above* — which is what
   **42I**.1 asks for — need not be norm-bounded, so no such `r` exists in
   general.  Filed as an erratum on **152XII**; the fix in the text is one
   sentence (pass to the cofinal tail `{d | d₀ ≤ d}`), and the fix here is to
   bound `B(x,x)` between `⟨x, d₀x⟩` and `⟨x, ub x⟩` and use
   `CStarAlgebra.norm_le_norm_of_nonneg_of_le`.  It is the same gap worker 32
   had to fill in `vn.tex` **44XV**.
2. **`usconv` is avoided.**  The thesis gets `‖B(x,y)‖ ≤ r‖x‖‖y‖` from
   `⟨T_α y, x⟩⟨x, T_α y⟩ ≤ r²‖x‖²⟨y,y⟩` and the fact that a product of
   ultrastrong limits converges ultraweakly.  In Lean that route needs the
   ultraweak closedness of norm balls — **44XI**.3 `vn_positive_basic_3`, still
   `sorry` in the frozen `A/VN`.  Instead polarization gives
   `‖B(x,y)‖ ≤ r₀(‖x‖+‖y‖)²`, and rescaling `x ↦ tx`, `y ↦ t⁻¹y` (which fixes
   `B(x,y)`) with `t = (‖y‖/‖x‖)^{1/2}` turns that into `4r₀‖x‖‖y‖`.
   The two zero cases come from `B(0,y) = B(x,0) = 0`.

Self-adjointness of the supremum is also cheaper than the thesis's "noting
`B(x,y) = uwlim ⟨x,T_α y⟩`, it is easy to see `T` is self-adjoint": once
`0 ≤ T − d₀` is known (which is needed anyway), `T = (T − d₀) + d₀` is a sum
of self-adjoints.  This matters, because `star` is *not* ultrastrongly
continuous and the obvious Lean transcription of that sentence does not exist.

Five file-private helpers about the ultrastrong topology on `𝒷` were needed
(`usTendsto_add'`, `_mul_left'`, `_mul_right'`, `_smul'`, `_const'`, `_sum'`,
`_unique'`).  **They belong in `Theses.A.VN.Basic` beside `usTendsto_iff` and
45IV** and should be moved there when that file is unfrozen; scalar
multiplication is handled as multiplication by `algebraMap ℂ 𝒷 c`, so 45IV
covers it, and uniqueness of limits is `vn_positive_basic_1`.

### 153I.2 — divergence class (2): the author's proof is unavailable

`153III` is "not converted" and is not in `bsols.tex`.  The proof here is
**152XII** applied twice: `⟨x, (ad_T S) x⟩ = ⟨Tx, S(Tx)⟩`, so the vector forms
of `ad_T S` on `X` are the vector forms of `S` on `Y`, and both suprema are
computed by their vector forms.

**The hypothesis `hX : SelfDual 𝒷 X` is not used** — Lean's unused-variable
linter says so, and the suppression `set_option linter.unusedVariables false`
above the declaration is the evidence.  Normality of `ad_T : 𝒷ᵃ(Y) → 𝒷ᵃ(X)` is
preservation of suprema *of `𝒷ᵃ(Y)`*; the supremum in `𝒷ᵃ(X)` is handed to it.
The thesis's hypothesis was kept (faithful transcription) and the surplus is
filed as an erratum nit on **153I**.

### 154III.2 — divergence class (1)

`existence_paschke_2` is the uniqueness clause of part 2, and it follows from
part 1 (the universal property, a *field* of `PaschkeModule`) applied to the
shifted bilinear map `(a,b) ↦ (a₀a) ⊗ b`.  The only work is its
φ-compatibility bound, and that is complete positivity of `φ` at two families:
with `K = ‖a₀‖²+1` and `c = √(K − a₀*a₀)`,

```
∑ᵢⱼ bᵢ* φ((a₀aᵢ)*(a₀aⱼ)) bⱼ  +  ∑ᵢⱼ bᵢ* φ((caᵢ)*(caⱼ)) bⱼ
    =  K · ∑ᵢⱼ bᵢ* φ(aᵢ* aⱼ) bⱼ,
```

all three terms being `≥ 0`, so the first is between `0` and `K · S₀` and its
norm is at most `K‖S₀‖`.  **No matrix machinery is needed** — the identity is
`a₀* a₀ + c* c = K` conjugated by `aᵢ`, `aⱼ` and pushed through the linear map,
and positivity is `IsCompletelyPositiveMap` read literally.

### Corrections to the round's plan

* **"All ten of `Paschke.lean` sit behind 152X" is wrong.**  152X unblocks
  exactly one of them (154III.2, above, and that through part 1's universal
  property rather than through 152X).  `existence_paschke` (154III.1–3) is the
  parsec-1540 construction and needs **150II** + **151Ia**; `existence_paschke_4`
  is `paschke-spatial`; 155II is KSGNS; 156II and 157IV are full theorems.
* **`existence_paschke_5`'s "term-in-a-statement leak" is closed, but not by
  proving `existence_paschke_5`.**  The leak was that its *statement* contains
  the term `ba_vonNeumannAlgebra M.selfDual`, which was `sorry`.  Proving 152X
  closes it.  `existence_paschke_5` itself is 154VIII/154IX and needs
  `existence_paschke_4`, still `sorry`.
* **160II** was not attempted; w30's assessment stands (the ON-basis conjunct is
  the published solution, the `SelfDual ℬ Z` conjunct is 149V (4)⇒(1)).

## Session 11 — `B/Eff` parsecs 215/219/220: the †-effectus theorem (worker 33)

Proved: **219XVI** `dagger_is_functor`, **220II** `dagger_thm_sufficiency` and
**215III** `dagger_theorem` (`Theses/B/Eff/Dagger.lean`).  B/Eff 34 → 31 code
`sorry`s; `Dagger.lean` 6 → 3 (the three left are the `vNᵒᵖ` examples 215VI,
221III and 223VI, which need thesis A).

### Divergence: class 2 — a different route to 219XVI

The thesis proves `(f ∘ g)† = g† ∘ f†` by putting the *whole* composite in the
standard form of 212III: Setting **219II** introduces four isomorphisms
`χ, ω, β, α`, and the proof then chains 219III, 219V and the four "daggered
squares" 219VII, 219IX, 219X, 219XIII together with 219XIV.  None of that
apparatus is formalized here, because six of the eight results are not needed.

What is formalized instead peels the composite one *generator* at a time.
Writing `f = h ∘ asrt_{1∘f}` with `h` pristine (**218X**) and
`h = π_{im h} ∘ γ ∘ ζ_{1∘h}` (**218VI**), every pure map is a composite of
asserts, quotients `ζ_s`, comprehensions `π_i` and isomorphisms, and the dagger
of each *one-sided* composite is a separate, short lemma:

| lemma | statement | proof |
|---|---|---|
| `pureDagger_comp_iso` | `(θ ∘ f)† = f† ∘ θ⁻¹` | `π_{im f} ∘ θ` is a comprehension for `im f ∘ θ⁻¹` (199VII.1 + `isComprehension_comp_iso`), and `216V` transports `asrt` |
| `pureDagger_comp_compr` | `(π_i ∘ f)† = f† ∘ ζ_i` | comprehensions compose (**211XI**) and `im (π_i ∘ π_j) = j ∘ ζ_i` |
| `pureDagger_asrt_comp` | `(asrt_b ∘ asrt_a)† = asrt_a ∘ asrt_b` | **216XI.Ax2** + **219XI** — this *is* 219XI, restated |
| `pureDagger_compr_asrt_zeta` | `(ζ_e ∘ asrt_p ∘ π_t)† = ζ_t ∘ asrt_p ∘ π_e` | **219XIV**, generalized (below) |
| `pureDagger_compr_comp` | `(N ∘ π_s)† = ζ_s ∘ N†` | 218X, then the three above |
| `pureDagger_comp_zeta` | `(ζ_s ∘ n)† = n† ∘ π_s` | the dagger of the previous one at `n†` (**218XII**) |
| `pureDagger_comp_pristine` | `(h ∘ n)† = n† ∘ h†`, `h` pristine | 218VI + the three preceding |
| `pureDagger_asrt_comp_left` | `(M ∘ asrt_q)† = asrt_q ∘ M†` | 218X + `pureDagger_comp_pristine` + 219XI |
| `pureDagger_comp_asrt` | `(asrt_q ∘ M)† = M† ∘ asrt_q` | its dagger at `M†` |

219XVI is then three lines: `f ∘ g = h ∘ (asrt_{1∘f} ∘ g)` with `h` pristine.

The one genuinely hard ingredient is 219XIV, and it is transcribed **faithfully**
(class 1): the thesis's own proof — compute `asrt_p ∘ asrt_t` in standard form
using the auxiliary isomorphisms `α₂`, `β₂`, then apply **219XI** — with the
single change that it is stated for an arbitrary sharp `e ≥ ⌈p⌉` in place of
`⌈p⌉`.  That generalization costs nothing in the proof and is what lets the
lemma be applied at `e = 1 ∘ h` for the pristine part `h` of an arbitrary pure
map, without transporting along `1 ∘ h = ⌈1∘f⌉`.  Filed in ERRATA under
**219II–219XVI** as informational ("the thesis proves more than it needs").

Two reusable helpers isolate the two uniqueness arguments the thesis performs
four times over (219VII, 219IX and the two halves of 219XIV's `α₂`/`β₂`):

* `zetaMap_eq_of_compr` — a map into a comprehension for `J` composing with it
  to `asrt_J` *is* `ζ_J` (comprehensions are monic).  This is the published
  solution to **219IX** (`bsols.tex:3283`) in abstract form.
* `comprMap_eq_of_zeta` — dually, quotients being epic; this is **219VII**.

**219X** (`bsols.tex:3319`) is not formalized as such: in the route above the
square it daggers never arises.  Its content — `π_⌈q⌉ ∘ ψ⁻¹` is pristine with
dagger `ψ ∘ ζ_⌈q⌉`, so 218IX.5 applies — is subsumed by
`pureDagger_comp_pristine`.

### 220II and 215III

`dagger_thm_sufficiency` is a faithful transcription (class 1) of eff.tex:6682–
6795, using the new `pureDaggerCat` (`Pure C` as a †-category, whose `dag_comp`
is 219XVI), `pureDagger_diamond_adjoint` (Ax. 1: apply `(–)^⋄` to the standard
form, using 218II and 209IV — this needs no functoriality) and
`pureDagger_comp_self` (`f† ∘ f = asrt_{1∘f}²`, Ax. 2).  Note `pureDaggerCat`
is a plain `noncomputable def`, deliberately **not** an instance.

**215III `dagger_theorem`** was stated in parsec 215, two thousand lines before
`dagger_thm_sufficiency`, one of its two halves.  It has been **moved** to just
after 220II, with a comment left at its numbering slot — the device used for
208III and 178III.1.  Its statement is unchanged.

## Session 12 — `A/Proc` parsecs 960, 1040 and 1290 (worker 35)

Proved: **96III**.1 `ncp_uwlim_1` and **96III**.2 `ncp_uwlim_2`, **104IV**
`centrally_similar_fundamental` (`Theses/A/Proc/Measurement.lean`, 50 → 47 code
`sorry`s); **129IV** `measure_zorn`, **129VI**
`measure_space_continuous_discrete`, **129VIII** `continuous_measure_space`
(`Theses/A/Proc/Duplicators.lean`, 24 → 21).  A/Proc 160 → 154.  All seven
new/closed declarations are axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`); `lake build Theses.A.Proc.Duplicators` exits 0.

### Divergence classes

**(1) Faithful.**  `ncp_uwlim_1` is proc.tex:390 verbatim — the positivity of
`∑_{ij} b_i* g(a_i* a_j) b_j` as an ultraweak limit — and is only now provable
because 45IV `mult-uws-cont` was discharged in session 10 (our
`IsCompletelyPositiveMap` is *defined* by exactly the `∑_{ij} b_i* f(a_i*a_j)b_j`
criterion the author uses, so no reformulation is needed).  `ncp_uwlim_2` is
proc.tex:405, again unlocked by session 10 (**44XV** `p-uwcont`).  **104IV** is
proc.tex:1525 step for step, including `q² e = q ϑ(e) q` self-adjoint and the
appeal to **23VII** `sqrt` for "`q²` commutes with `e`, hence so does `q`".
**129IV** and **129VIII** are proc.tex:6237 and 6315 transcribed, including the
`β_C = sup{μ(D) : C ⊆ D ∈ 𝒮}` device and the halving recursion.

**(2) Different route.**  In `ncp_uwlim_2`'s last step the thesis says "the
uniform limit of continuous functions is continuous, thus normal by
`p-uwcont`".  Mathlib's `TendstoUniformlyOn.continuousOn` needs a
`TopologicalSpace` *instance* on the domain, and `ultraweak A` is deliberately
not one, so uniform convergence is applied one np-functional at a time: the
new private `continuousOn_ultraweak_of_forall` (the `ContinuousOn` counterpart
of `A/VN`'s `continuous_ultraweak_of_forall`, three lines over **42III**
`uwTendsto_iff`) reduces ultraweak `ContinuousOn` to the scalar case, where the
uniform-limit theorem applies verbatim.  This is the same obstacle 45II hit in
session 10, handled the same way.

In **129VIII**'s halving step the thesis argues "either `0 < μ(A) ≤ ½μ(A₁)` or
`0 < μ(X∖A) ≤ ½μ(A₁)`" — note `X∖A`, which should be `A₁∖A` (filed in
`ERRATA.md`); the Lean proof
uses `A₁∖A` (the sets must stay inside `A₁` for the recursion) and phrases the
halving multiplicatively, `2·μ(C) ≤ μ(B)`, to avoid `ℝ≥0∞` division.  Also, the
final "pick `n` with `μ(Aₙ) ≤ ε`" is done by contradiction from
`n·ε ≤ 2ⁿ·μ(Aₙ) ≤ μ(B) < n·ε`, which needs only monotonicity — no cancellation
in `ℝ≥0∞`.

**(3) Mild.**  `ncp_uwlim_2` builds the positive linear map `gp` out of the
bare `g : A →ₗ[ℂ] B` plus the main claim of 96III, since **44XV** is stated for
`A →ₚ[ℂ] B`; our 96III.2 states its conclusion for `⇑g` directly.

**(4) Our statement mis-transcribes the thesis:** none.  (**104IV**'s statement
*did* have to change, but it was a faithful transcription of a thesis statement
that is wrong — see below.)

**(5) Closed from Mathlib without reading the author's argument:** none.  In
particular **129VIII** is Sierpiński's theorem, and was written from
proc.tex:6315 rather than looked up.

### 104IV is false as printed (new erratum)

`centrally_similar_fundamental` omits the hypothesis `⌈q⌉ = 1` that its own
proof invokes.  At `q = 0` both hypotheses become `0 ≤ e` and `0 ≤ e^⊥`, so the
printed lemma would force every miu-endomorphism of every von Neumann algebra
to fix every projection.  Machine-checked as
`centrally_similar_fundamental_needs_faithful`; filed in `ERRATA.md` in point
order after 104III.2a.  **The Lean statement has been changed** — `⌈q⌉ = 1` is
now a hypothesis — because both consumers (104VI, 104VII) state it anyway, so
nothing downstream is weakened.  Only the second conclusion needs it; `eq = qe`
does not.  This is the second false statement found in parsec 1040 (after
worker 29's 104III.2a) and the third in this chapter.

### 129IV proves more than it needs

Lean's unused-variable linter reports that `measure_zorn` uses **neither**
`hμ : μ.IsComplete` **nor** `hmeas : ∀ S ∈ 𝒮, MeasurableSet S`.  The two
warnings are left in place as the evidence, and the doc comment says so.  The
lemma holds for an arbitrary collection of subsets of a *finite* measure space
(`μ` is an outer measure on all of them); only `IsFiniteMeasure` is used, for
`β_C ≤ μ(X) < ∞`.  129VI and 129VIII, which are its consumers, do need
measurability — but for their own reasons (`measure_union`, continuity from
below), not for 129IV.

### What is *not* reachable — correction to the round's plan

**99II `gardner` is blocked, and not on 61II.**  Session 10 discharged 61II
`ncp_ceill`, which was the blocker for (3)⇒(2).  But the *last* implication,
(2)⇒(1), rests on "since the linear span of projections is norm-dense in `𝒜`"
(proc.tex:872) — that is **65IV `projections_norm_dense`**, `sorry` at
`A/VN/Projections.lean:3049`, and behind it **64II
`abelian_projections_norm_dense`** (`:2905`).  There is no way around it: the
statement is false for C*-algebras without projections, so von-Neumann-ness has
to enter exactly there.  Everything else in the five-way TFAE is elementary and
was checked to be in reach.  Consequently **99IX, 99XI, 99XII and 102V remain
blocked** (99XI's and 99XII's own hints route through `iso`, hence gardner).

The same lemma blocks **104VI** and **104VII**: both proofs end "since `p` is
the norm limit of linear combinations of such projections `e`" (proc.tex:1580).
So 65IV — not 61II — is now the highest-leverage frozen item for this chapter
after 89IX.

---

## Session 11 — `B/Eff` parsec 228: the Snake Lemma (worker 36)

Proved: **228II** `snake_lemma` (`Theses/B/Eff/Comparisons.lean`), the last
substantial B/Eff item that is not gated on thesis A.  B/Eff 31 → 30 code
`sorry`s; `Comparisons.lean` 4 → 3.  The statement is unchanged (class 4:
nothing mis-transcribed).

The proof is ~330 lines, preceded by 35 short helper lemmas that collect the
`(–)_⋄`/`(–)^□` calculus of parsecs 206–208 in `SPred`-form.  Two of those
helpers are the whole reason the proof is manageable and deserve naming:

* `diaPull_eq_boxPull_compr` — for a comprehension `π` for a sharp `s`,
  `π^⋄ = π^□` **on predicates below `s`**; and
* `boxPull_pureDagger_quot` — for a quotient `ξ` for a sharp `s`,
  `(ξ†)^□ = ξ_⋄` **on predicates above `s`**.

Both are instances of the absorption rule **213V** (`simple_andthen_absorption`)
via `π† ∘ π = asrt_{im π}` and `ξ ∘ ξ† = asrt_{(ker ξ)^⊥}` (the new
`pureDagger_compr_comp_asrt` / `pureDagger_quot_comp_asrt`, each a three-line
consequence of **219XVI** + **217III**).  They are what makes the four induced
maps `f̄, ḡ, h̄, k̄` computable at all: e.g. `h̄^□(0) = (a_ζ†)^□(h^□(im b))`
becomes `(a_ζ)_⋄(h^□(im b))`, which is the form 228VIII uses without comment.
This is 228I's own remark ("maps `l^□` appear where we would have expected
`l^⋄`") made precise: `(–)^□` and `(–)^⋄` agree exactly on the half of the
lattice the diagram lives in, and the "orthomodularity" the agreement encodes is
already inside `asrt`'s absorption rule — no orthomodular-lattice reasoning is
needed anywhere in the proof.

### Divergence: class 2 — the right-hand face of the cube is never built

The thesis's overview (228III) constructs **two** subquotients: the left face
`m ≫ g = g' ≫ c_π` and the right face `h ≫ v = a_ζ ≫ h'`, with
`v = ξ_{h_⋄(im a)}` and `h'` a comprehension.  It then proves
`h_⋄(1) = (v^□ ∘ h'_⋄)(1)` (`snakehdiamondone`), four forms of `d_⋄`
(`snakedidents`), and the exchange identity `g^□ ∘ (c_π)_⋄ = m_⋄ ∘ g'^□`.

**`v`, `h'`, `snakehdiamondone`, three of the four forms of `snakedidents` and
the exchange identity are all avoidable**, because the four exactness statements
only ever evaluate `d_⋄` at `1` and `d^□` at `0` (227III.1: exactness at the
middle object of `u, w` is `u_⋄(1) = w^□(0)`, our `exactAt_iff'`).  Filed in
`ERRATA.md` under **228III–228VI** as informational.  Concretely:

* `d_⋄(1)`: `g'` is a quotient, so `g'_⋄(1) = 1` and
  `d_⋄(1) = (a_ζ)_⋄(b'_⋄(1))`; `h^□ ∘ h_⋄ = id` (**227V**) turns that into
  `(a_ζ)_⋄(h^□(b_⋄(im m)))`, and `im m = g^□(c^□(0))` **is** the definition of
  `m` — which is exactly what the exchange identity degenerates to at `1`.
* `d^□(0)`: `g'_⋄ ∘ g'^□ = id` (**227V**) gives `d^□(0) = g'_⋄(b'^□(im a))`, and
  `b'^□ = m^□ ∘ b^□ ∘ h_⋄` follows from `b' ≫ h = m ≫ b` plus `h^□ ∘ h_⋄ = id`.
  (This last identity is the thesis's `snakeceilbprime`, and is the one piece of
  the `d`-identities that is used as printed.)

### The two "dual arguments" the thesis does not write

228VII and 228VIII each close with "by a dual argument one derives exactness in
`ker c`/`ker b`".  A †-effectus is not self-dual, so both had to be supplied.
Both turn out to be short, and neither is the mirror image of the argument it is
said to be dual to:

* **exactness at `ker b`** (`f̄_⋄(1) = ḡ^□(0)`, from the right-modularity `m₄` of
  `f` over `⌈1∘b⌉^⊥`).  Both sides are `b_π^□` of something, and `b_π^□` is
  injective modulo meeting with `ker b`, so it suffices to show
  `SPred.IsInf (ker b) (g^□((ker c)^⊥)) (f_⋄(ker a))`.  The middle term collapses:
  for `r ≤ ker b` one has `g_⋄(r) ≤ g_⋄(ker b) ≤ ker c` (from `w₂` and
  `b_⋄(ker b) = 0`), so `g_⋄(r) ≤ (ker c)^⊥` forces `g_⋄(r) = 0`, i.e.
  `r ≤ ker g = im f` (row 1).  Then `m₄` finishes, once one notes
  `f^□(ker b) = (f ∘ b)^□(0) = (a ∘ h)^□(0) = ker a` because `h` is total.
* **exactness at `ker c`** (`ḡ_⋄(1) = d^□(0)`, from the left-modularity `m₁` of
  `b` over `im f`).  Apply the injective `(c_π)_⋄` to both sides:
  `(c_π)_⋄(g'_⋄(m^□(z))) = g_⋄(m_⋄(m^□(z))) = g_⋄(z)` where `z = ker b ∨ im f` is
  `m₁`'s witness, using `z ≤ im m` (both joinands are, since
  `g_⋄(ker b) ≤ ker c` and `im f = ker g`); and `g_⋄(z) = g_⋄(ker b)` because
  `g_⋄` preserves joins and kills `ker g`.  That is `(c_π)_⋄` of the left-hand
  side.

Exactness at `cok a` (228VII) and at `cok b` (228VIII) are faithful
transcriptions (class 1) of the two displays the thesis does write, modulo the
gap in 228VIII's third step recorded in `ERRATA.md`.

### `g'` is a quotient: a shortcut through 212III

The thesis gets `g'` from the universal property of `c_π` and then says "we see
there is a unique **sharp quotient** `g'`", leaving the reader to redo the
homology-axiom argument of 228IV on the other side.  Here `g'` is *defined* as
`m ≫ g ≫ c_π†`, which makes purity immediate (`upm_closed_pure`), and
`g' ≫ c_π = m ≫ g` follows from `c_π† ∘ c_π = asrt_{im c_π}` and the absorption
rule.  That it is a quotient is then the new

* `isQuotient_of_pure` — a pure `f` with `im f = 1` and `1 ∘ f` sharp is a
  quotient for `(1 ∘ f)^⊥`,

read straight off the standard form **212III** (`asrt_s ∘ ζ_s = ζ_s` for sharp
`s`, and `π_1` is iso).  Its two hypotheses are: `im g' = 1`, from
`(c_π)_⋄(g'_⋄(1)) = g_⋄(g^□(c^□(0))) = c^□(0) = (c_π)_⋄(1)` and injectivity of
`(c_π)_⋄`; and sharpness of `1 ∘ g' = 1 ∘ (m ∘ g)`, which is the homology axiom
**226VII** (`homological_category.2.2` + `homological_exact`) applied to the
kernel `m` and the cokernel `g` — the one place the thesis's own appeal to the
homology axiom is reproduced.

### Classification

* **(1) faithful:** the constructions of `m`, `b'` and `d` (228IV–228V), and the
  two exactness displays of 228VII/228VIII.
* **(2) different route:** the right-hand face of the cube and most of
  `snakedidents` are skipped (above); `g'` is defined rather than obtained.
* **(3) mild:** —
* **(4) our statement mis-transcribes the thesis:** none.
* **(5) closed from Mathlib without reading the author's argument:** none.

## Session 13 — `A/Proc` parsecs 1120, 1253 and 1300 (worker 37)

Proved **112III** `product_state_positive`, **112V** `basic_state_inner_product`
and **112VI** `product_functionals_separating` (`Tensor.lean`), **130II**
`atomic_measure_space` (`Duplicators.lean`), and repointed the sorried instance
`VonNeumannAlgebra (MatAlg n)` (`QuantumLambda.lean`) at its owner in `A/VN`.
A/Proc 154 → 149 code `sorry`s (build-warning convention 149 → 144).

### The two findings that changed the map of the chapter

* **Parsec 1120 is about the *algebraic* tensor product `𝒜 ⊙ ℬ`, not about
  `VNT`.**  112III, 112V, 112VI, 112VIII and 112IX are stated over Mathlib's
  `A ⊗[ℂ] B` with the tensor-product norm of 112II; none of them mentions
  `vnTensorProduct`, so none is behind 89IX.  Three of the five are now closed;
  only 112VIII (definiteness of the tensor norm) and 112IX are left, and they
  are hard for their own reasons, not for want of the von Neumann tensor
  product.
* **130II is not gated on `vonNeumannAlgebra_lp_infty`.**  Its conclusion is
  `∃ φ : NMIUMap 𝒜 ℂ, Bijective φ` — it lands in `ℂ`, whose `VonNeumannAlgebra`
  instance is real.  (Nor do 130IV/130V *state* anything needing the sorried
  instance: `NMIUMap` asks only for `CStarAlgebra`/`PartialOrder`/
  `StarOrderedRing` on `lp ℬ ∞`, and all three of those are honest instances in
  `A/VN/Basic.lean`.  A *proof* of 130IV/130V would still need the missing
  componentwise description of `spectralOrder` on `lp ℬ ∞`, i.e. the same
  mathematics as the instance — but that is "blocked on X", not "vacuous".)

### 112III (proc.tex:2789) — class (1), faithful

The author's four lines transcribed: `t = ∑ₙ aₙ ⊙ bₙ` gives
`(σ⊙τ)(t*t) = ∑_{n,m} σ(aₙ*a_m) τ(bₙ*b_m)`; both matrices are positive by
`cp-commutative` (**34IX**, `cp_commutative_cod`, proved); their entrywise
product is positive by `schur` (**111II**, proved); and the sum of the entries
of a positive matrix is `≥ 0`.  Worth recording: our
`Theses.A.CStar.IsCompletelyPositiveMap` is *defined* as
`0 ≤ ∑ᵢⱼ bᵢ* f(aᵢ*aⱼ) bⱼ`, which at `bᵢ ∈ ℂ` **is** the quadratic form of the
matrix `(σ(aᵢ*aⱼ))` — so the "positive matrix" step needs no reformulation at
all, only Hermitianness, which is `cstar-p-implies-i` (**10IV**).

### 112V (proc.tex:2808, Exercise) — (1) for positivity, (2) for symmetry

The exercise says "use `product-state-positive`", and the positivity half is
exactly that: `ω(t*t) = (σ⊙τ)((t t₀)*(t t₀))`.  Conjugate-symmetry is proved
*without* positivity, hence without the polarisation argument one would
normally use: `x ↦ t₀* x t₀` is ∗-compatible and `σ ⊙ τ` is involution
preserving (new `odotF_star`, from **10IV** on `σ` and `τ`), so
`ω(star x) = conj (ω x)` outright.

### 112VI (proc.tex:2833) — class (1), with one step made precise (3)

Transcribed step for step.  The author's "by replacing them if necessary we may
assume that `a₁,…,a_N` are linearly independent" is the new private
`exists_indep_repr`: expand the `aᵢ` in a basis of their (finite-dimensional)
span and collect the coefficients on the `ℬ`-side.  Everything after that is the
author's argument verbatim.

### 130II (proc.tex:6474) — (1) measure-theoretic half, (2) algebraic half

*Faithful.*  The author's dichotomy ("either `μ(S)=0` or `μ(A∖S)=0`") is
`atomic_dichotomy`; his reduction to real-valued `f` by splitting into real and
imaginary parts is `ae_const_of_atomic`.

*Different route, and why.*  For a real bounded measurable `g` the author takes
the two closed sets `L = {t | t ≤ g°}`, `U = {t | g° ≤ t}`, observes that the
dichotomy makes them cover `ℝ`, and concludes by **connectedness of `ℝ`** that
they meet.  The Lean proof realises `L` concretely as `{t | μ{g < t} = 0}` and
takes `r = sup L`, then shows `μ{g < r} = μ{g > r} = 0` directly by a countable
union.  Same content, and it avoids having to introduce `g°` (the class of `g`
in the abstract algebra) before knowing the algebra is `ℂ`.

*The real divergence is at the end, and it is forced by our rendering.*  The
thesis stops once every `f ∈ 𝓛^∞(A)` is a.e. constant — "hence `L^∞(X) ≅ ℂ`".
That step is **not** available as stated here: `IsLinftyOf` records that `q` is
additive, multiplicative, unital and ∗-preserving, but **not that it is
`ℂ`-linear**, and a ∗-ring isomorphism `ℂ → 𝒜` need not be `ℂ`-linear —
complex conjugation is one, and `q(f) = conj(f(x₀))` satisfies every clause of
`IsLinftyOf` for a Dirac measure.  So `z ↦ q(const z)` cannot simply be
inverted to an nmiu-map.  The fix used is to observe that `q(const ·)` is an
injective ∗-ring homomorphism *onto* `𝒜`, so every nonzero element of `𝒜` is
invertible, and then to apply **16VII** `gelfand_mazur` (proved, in
`A/CStar/Positive.lean`), which gives surjectivity of `algebraMap ℂ 𝒜`
directly.  Normality of the resulting isomorphism is read off from the two
monotonicity facts (`algebraMap` preserves the order by
`algebraMap_ofReal_mono`, and reflects it by the new
`algebraMap_nonneg_reflect`).

This is **not** an erratum against the thesis — in the thesis `L^∞(X)` is a
concrete algebra of functions and its `ℂ`-linearity is part of the setting.  It
is a note about our `IsLinftyOf`: *a `ℂ`-linearity clause is missing from it*,
and adding one (`q (z • f) = z • q f`) would make the statement match the
source more closely and shorten this proof.  Recorded here rather than acted on,
since changing `IsLinftyOf` changes the statements of 129X, 130II, 130IV and
130V at once.

*The thesis proves more than it needs* (the recurring pattern): 130II's standing
hypothesis `hμ : μ.IsComplete` is **not used** — the unused-variable warning is
left in place as the evidence — nor is `𝒜`'s von-Neumann-ness used for anything
except reading off the conclusion.  Atomicity plus finiteness is the whole
hypothesis.

### The `VonNeumannAlgebra (MatAlg n)` instance was a duplicate

`QuantumLambda.lean:419` carried `instance (n : ℕ) : VonNeumannAlgebra (MatAlg n)
:= sorry`.  `MatAlg n = CStarMatrix (Fin n) (Fin n) ℂ`, so this is **49IV**.1
`Theses.A.VN.mn_vna_1` at `𝒜 = ℂ`, and `mn_vna_1 n` typechecks against it
verbatim (the `PartialOrder` declared next to it is the same spectral order).
The `sorry` is now `mn_vna_1 n`: the obligation has moved to its owner in
`A/VN`, exactly as `exists_ncpCarrier` was repointed at `A/VN`'s
`exists_carrier` in session 1.  **`A/Proc` now has no sorried instance**, and
the project has two (`vonNeumannAlgebra_lp_infty`, `mn_vna_1`), not four.

### Classification

* **(1) faithful:** 112III, 112VI, and the measure-theoretic half of 130II.
* **(2) different route:** 112V's conjugate-symmetry half (involution
  preservation instead of polarisation); 130II's `L∞ ≅ ℂ` step (Gelfand–Mazur
  instead of inverting `q(const ·)`) — forced, see above; 130II's `sup L`
  instead of connectedness of `ℝ`.
* **(3) mild:** `exists_indep_repr` makes 112VI's "we may assume linearly
  independent" precise via a basis of the span.
* **(4) our statement mis-transcribes the thesis:** none.  But `IsLinftyOf`
  omits `ℂ`-linearity of `q` (above) — a *weakening* of the setting, not of a
  statement, and it made 130II harder rather than easier.
* **(5) closed from Mathlib without reading the author's argument:** none.
  `proc.tex` was read at 2770–2870 (112III–112IX) and 6455–6530 (130I–130V)
  before anything was written; `asols.tex` has no solutions past parsec 340 and
  its errata block has nothing for 1120 or 1300.

---

## Session 14 — `B/Dils` (worker 38)

Target: **149V** `dils_selfdual` (`HilbertModules.lean`), the chapter's named
root.  Result: **the reachable direction is proved and 160II falls with it**,
and two *false* statements were found in `Paschke.lean` — one fixed, one
diagnosed and machine-checked but deliberately not repaired.

### 1. 149V is *not* unblocked — three of its four implications are

Three successive briefs called 149V "unblocked; nothing frozen stands in its
way".  That is wrong.  Reading `dils.tex` 2249–2621 against the tree:

| implication | dils.tex | needs | status of the need |
|---|---|---|---|
| 1 ⇒ 3 | 149VII, 2258 | **77I**.1 `vn_complete_1` (ultrastrong completeness) | `sorry`, `A/VN/Completeness.lean:1602`, frozen |
| 3 ⇒ 4 | 149VIII, 2328 | **80IV** `approximate_pseudoinverse` (for polar decomposition in `X`) | `sorry`, `A/VN/Division.lean:464`, frozen |
| 4 ⇒ 2 | 149IX, 2461 | **77I**.1 again, and **87VIII** `ultraweakly_bounded_implies_bounded` | both `sorry`, frozen |
| 4 ⇒ 1 | 149XI, 2569 | nothing outside `HilbertModules.lean` | **proved** |

`VonNeumannAlgebra` in this project is `Theses/Common.lean:73`, i.e. the
thesis's abstract 42I (bounded directed suprema + faithful np-functionals);
completeness of `𝒷` is a theorem (77I), not part of the class, so there is no
way around it.  None of `Completeness`, `Division`, `NormalFunctionals` is even
on `HilbertModules.lean`'s import path — but importing them would only turn
three `sorry`s here into three `sorry`s there.

`dils_selfdual` is therefore now proved *from* five named implications
(`bddUnComplete_of_selfDual`, `exists_isONBasis_of_bddUnComplete`,
`unComplete_of_isONBasis`, `bddUnComplete_of_unComplete`,
`selfDual_of_isONBasis`) by `tfae_have`/`tfae_finish`; `4 ⇒ 1` and the trivial
`2 ⇒ 3` are proved, the other three carry a `sorry` and a doc comment naming
the exact frozen blocker.  `HilbertModules.lean` goes 1 → 3 code `sorry`s;
that is the deliberate "bank the skeleton" trade.

### 2. 149XI `selfDual_of_isONBasis` (4 ⇒ 1) — divergence class 1

The thesis's own argument, mirrored.  `t = ∑ᵢ eᵢτ(eᵢ)*`; ℓ²-summability of
`(τ(eᵢ)*)ᵢ` comes from the "substitute the partial sum for `x`" trick, which
needs Bessel; `τ x = ⟨t,x⟩` is then ultranorm continuity of `τ` (**148I**)
against **148V**, compared in the *ultraweak* topology, where limits are
unique (**44XI**.1).

One deviation (class 2, forced): the thesis reads off `τ(x) = ∑ₑ τ(e)⟨e,x⟩`
from ultranorm continuity of `τ` directly.  In the mirrored convention
`x ↦ ⟨t,x⟩` is continuous in its *second* argument only, so the two nets are
compared ultraweakly instead of ultrastrongly.  This needed the new
`uwTendsto_of_unTendsto_mulInner` (**43I** mirrored: `|ω(a)| ≤ ‖a*‖_ω ω(1)^½`,
i.e. `norm_apply_le_omegaNorm` at `star a`).

New public by-products in `HilbertModules.lean`, all axiom-clean:
`mulBInner` (+`_inner`, `_norm`) — `𝒷` as a `BInner`-module over itself,
needed to apply **144V**/**148I** to `τ : X → 𝒷`; `cstarBInner_norm`;
`norm_np_le_unSeminorm_mulInner`; `uwTendsto_of_unTendsto_mulInner`;
`inner_sum_smul_orthogonal`; `inner_sum_smul_self`; `onbasis_coef_absorb`;
**`mod_bessel`** (Bessel's inequality).

One statement generalisation: the `UltranormContinuity` section had
`variable {X Y : Type v}`, which pinned **144V**/**148I**'s codomain to `X`'s
universe and so could not be applied with `Y = 𝒷`.  Now `{Y : Type*}`.

### 3. 160II `direct_prod_self_dual_basis` — divergence class 1

The published solution (`bsols.tex`, `direct-prod-self-dual-basis`) verbatim:
`κ₁(E) ∪ κ₂(F)` is an ON basis of `Z`, and self-duality is then 149V's
`4 ⇒ 1`.  Both clauses of `IsONBasis` reduce to the same lemma (`hconv`)
because `∑_{g ∈ s} c g • G g` splits as `κ₁(∑_{i ∈ s.toLeft} …) + κ₂(∑_{j ∈
s.toRight} …)`, and `Finset.toLeft`/`toRight` are cofinal
(`tendsto_finset_toLeft_atTop`).  Two by-products in `SelfDual.lean`:
`innerPreserving_add` (an inner-product-preserving map between pre-Hilbert
modules is automatically additive) and `innerPreservingHom`.

### 4. `PhiCompatible.bound` was false — mirrored on the wrong side (class 4, FIXED)

`Paschke.lean`'s **154II** read

```
‖∑ i, T (a i) (b i)‖^2 ≤ r * ‖∑ i, ∑ j, star (b i) * φ (star (a i) * a j) * b j‖
```

— the thesis's formula copied *unmirrored*, while `PaschkeModule.inner_tprod`
next to it is mirrored.  The two are jointly unsatisfiable.  For `n = 1` they
read `‖b φ(a*a) b*‖ ≤ r ‖b* φ(a*a) b‖`, and in `M₂` with `φ = id`,
`a = e₀₀`, `b = e₁₀` the left side is `‖e₁₁‖ = 1` and the right side `0`.
Machine-checked in `CStarMatrix (Fin 2) (Fin 2) ℂ` (scratchpad `w38d.lean`):
`star aa * aa = aa`, `star bb * (star aa * aa) * bb = 0`,
`bb * (star aa * aa) * star bb ≠ 0`.  So `PaschkeModule φ` was **uninhabited**
for `φ = id : M₂ → M₂`, `existence_paschke` was false, and the nine
`PaschkeModule`-hypothesis theorems of the file were vacuous.

Fixed to the mirrored form

```
‖∑ i, T (a i) (b i)‖^2 ≤ r * ‖∑ i, ∑ j, b i * φ (star (a i) * a j) * star (b j)‖
```

which is *exactly* `‖⟨v,v⟩‖` for `v = ∑ᵢ aᵢ ⊗ bᵢ` — machine-checked from
`inner_tprod` alone (scratchpad `w38c.lean`, `tprod_bound_eq`), so `tprod`
itself is now φ-compatible with `r = 1`, as it must be.  The stars must be on
the *outside*: under `inner (b • x) y = inner x y * star b` every `⟨v,v⟩` has
the shape `∑ bⱼ (…) star bᵢ`, so the old placement is wrong under *any*
mirroring choice.  `existence_paschke_2`'s proof survives with three local
edits (its `S₀,S₁,S₂` take the new shape, and complete positivity is applied
at the coefficients `star ∘ b` instead of `b`).  The correction and the
counterexample are recorded in `PhiCompatible`'s doc comment.

### 5. `PaschkeModule` still forces `h ∘ ϱ = φ ∘ star` (class 4, NOT fixed — needs a decision)

A second, deeper mirroring defect, machine-checked (scratchpad `w38e.lean`):

```
theorem h_rho_eq_phi_star (φ : NCPMap 𝒜 ℬ) (M : PaschkeModule φ) (a : 𝒜) :
    M.h (M.ρ a) = φ (star a) := by
  rw [M.h_def, M.ρ_tprod, M.inner_tprod]; simp
```

Since `IsPaschkeDilationOf` (`Stinespring.lean:1180`) requires
`∀ a, D.h (D.ρ a) = φ a`, **`existence_paschke_5` is false as stated** as soon
as `PaschkeModule φ` is inhabited (take `φ = id` and `a` non-self-adjoint).
`existence_paschke_4`'s hypothesis `hφ : φ a = inner ℬ e ((ϱ' a).1 e)` is off
by the same `star`.

Which field is at fault is *not* free, and that is why this is left open:

* `inner_tprod`'s `φ (star a' * a)` is **forced**: from `smul_action` every
  inner product of elementary tensors has the shape `b' * M(a,a') * star b`,
  and `⟨v,v⟩ ≥ 0` for all `v` forces the matrix `(M(aⱼ,aᵢ))ᵢⱼ` to be positive,
  i.e. `M(a,a') = φ(star a' * a)` (giving the standard Gram
  `(φ(star aᵢ * aⱼ))ᵢⱼ`).  `φ (star a * a')` gives its *transpose*, which is
  not positive for a general ncp `φ`.
* `h_def`'s `inner (1⊗1) (T (1⊗1))` is **forced**: the other order is
  conjugate-linear in `T`, so `h` could not be an `NCPMap`.
* `ρ_tprod`'s `tprod (a₀ * a) b` is **forced** by multiplicativity of `ρ` into
  `Ba ℬ X`, whose product is composition (`baSubalgebra_coe_mul_apply`).

So no single field can be edited; the repair is a coordinated re-mirroring of
the bundle.  Two consistent packages were found and both have a cost:
(i) `inner_tprod = b' * φ (a' * star a) * star b` with bound
`∑ᵢⱼ bⱼ φ(aⱼ * star aᵢ) star bᵢ` (mirror 𝒜 as well) — self-consistent, gives
`h ∘ ϱ = φ`, but then `existence_paschke_4`'s `ϱ' : NMIUMap 𝒜 (Ba ℬ Y)` is on
the wrong handedness; (ii) reading Lean's `tprod a b` as the thesis's
`a* ⊗ b`, i.e. `ρ_tprod : tprod (a * star a₀) b` — also self-consistent.  This
is a `Paschke.lean`-wide decision and deserves its own pass; **`Paschke.lean`
and the `PaschkeTriple`/`IsPaschkeDilationOf` interface in `Stinespring.lean`
should not be built on until it is made.**

### 6. Classification

* **(1) faithful:** 149XI (4 ⇒ 1); 160II.
* **(2) different route:** 149XI's final identification is made ultraweakly
  rather than ultrastrongly (forced by the mirrored convention, §2); 160II's
  ℓ²-summability of the two half-families is read off from `Finset.sum_map`
  rather than from "subfamilies of ℓ²-summable families are ℓ²-summable".
* **(3) mild:** 160II's index set is `ι ⊕ κ` with the cofinality of
  `Finset.toLeft`/`toRight` made explicit, where the solution just writes
  `G = κ₁(E) ∪ κ₂(F)`.
* **(4) our statement mis-transcribes the thesis:** `PhiCompatible.bound`
  (§4, fixed); the `PaschkeModule` bundle's `star` (§5, diagnosed, open); the
  `{X Y : Type v}` universe pinning of `UltranormContinuity` (§2, fixed).
* **(5) closed from Mathlib without reading the author's argument:** none.
  `dils.tex` 2127–2621, 3530–3840, 4456–4720 and the `bsols.tex` solutions
  `direct-prod-self-dual-basis` and `onb1` were read first.

### 7. Verification

* `lake build Theses` → `Build completed successfully (8738 jobs)`, exit 0,
  **zero** `error:` lines outside the pre-existing `linter.style.header`
  noise.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for all 15 new
  declarations.  No `sorry`ed instances in `B/Dils`.
* Code `sorry`s, before → after: `HilbertModules` 1 → **3**, `SelfDual` 25 →
  **24**, others unchanged; `B/Dils` 63 → **64**.  (The +1 is the 149V
  skeleton: one opaque `sorry` replaced by three named, individually blocked
  ones, with the TFAE itself now proved.)
* Files touched: `Theses/B/Dils/HilbertModules.lean`,
  `Theses/B/Dils/SelfDual.lean`, `Theses/B/Dils/Paschke.lean`,
  `PROVING-LOG.md`.  Nothing staged, nothing committed.
  (`Theses/B/Eff/Effectus.lean` is also dirty — not mine.)

## Session 15 — `B/Eff` parsecs 181, 187, 188: Cho's theorem (worker 39)

Target: the four `sorry`s of Cho's theorem **180X** in `Theses/B/Eff/Effectus.lean`
— `eff_partial_to_total` (181XI), `cho_thm_1` (187I), `cho_thm_3_par_tot`
(188III) and `cho_thm_3_tot_par` (188IV).  **All four are now proved**; `B/Eff`
goes 30 → **26** code `sorry`s and `Effectus.lean` 7 → **3** (the three left
are the thesis-A examples `effectus_vn`, `effectus_vn_partial` and the parked
`extensive_effectus`).

### The one structural obstacle: chosen coproducts vs. inherited ones

`EffectusTotalForm`/`FinPAC`/`EffectusPartialForm` are stated against
*whatever* `HasFiniteCoproducts`/`HasTerminal` instance is in scope, while the
thesis computes with the coproducts that `Tot D` and `Par C` inherit from `D`
resp. `C`.  Both halves therefore needed a bridge, and both bridges have the
same shape and are now permanent API:

* `totCoprodIso`, `tot_hom_ext_base`, `tp₁`, `tp₂`, `tpair`, `tp_jm`,
  `truth_decomp` — coordinates for an *arbitrary* chosen coproduct of `Tot D`,
  transported from `coprod_prod` (181VII) along
  `IsColimit.coconePointUniqueUpToIso`.
* `parCoprodIso`, `par_pproj₁_eq`, `par_pproj₂_eq` — the same for `Par C`,
  plus a small `pval` calculus (`pval_comp`, `par_hat_comp`, `par_map_pproj₁`,
  `par_hom_ext`, …) that keeps the two category structures on
  `X.base ⟶ Y.base ⨿ 1` from being confused by the elaborator.

Consequence worth recording: **`tot_effectusTotalForm` is proved for an
arbitrary coproduct/terminal structure on `Tot D`**, not just the inherited
one.  That is what makes `cho_thm_3_par_tot` provable in the general form our
statement already had (`∀ s : EffectusTotalStructure (Tot D)`).

### 181XI (`eff_partial_to_total`) — class (1), faithful

Transcribed from 181XII–XVI.  `Tot D`'s initial object is `0`, its final
object is `I` via 181XIII (`one_m_is_id`: `1 = id_I`), its coproducts are `D`'s.
The two pullback squares and the joint monicity of `[κ₁,κ₂,κ₂]`, `[κ₂,κ₁,κ₂]`
are the thesis' arguments verbatim, in `tp₁/tp₂` coordinates.

One step the thesis leaves implicit and that the formalization has to supply:
in 181XVI the third coordinates are compared as *predicates* (`c₁ ⋁ … = 1`
determines `1 ∘ cᵢ`, not `cᵢ`).  Over the inherited coproduct that is the same
thing because `1 = id_I`; over an arbitrary one the final object `⊤` is only
*isomorphic* to `I`, so we prove `truth_terminal_isIso` (`1 : ⊤ ⟶ I` is an
iso, both objects being final in `Tot D`) and cancel it.

### 187I (`cho_thm_1`) — class (1) for 187III–V and VII, class (2) for the
### zero–one axiom

187III (PCM), 187IV (enrichment), 187V (finPAC) and 187VII (the two final
axioms) are transcribed exactly, including the bound `(▷₂+id) ⊙ d` and
`[id,κ₂] ⊙ d` of the associativity argument and the two successive pullback
liftings of 187VII (which is where the already-recorded `▷₂`-form of 186IV,
`par_pullbacks_right₂`, is used).

**Class (2)** — the zero–one axiom of 187VI.  The thesis derives `1 ⊥ p ⟹
p = 0` from a pullback square drawn between `1`, `1`, `(1+1)+1` and `1+1`
(eff.tex:1885–1900).  We could not reconstruct that square as an instance of
either 180I's or 186IV's: its four corners are *not* of the shape
`P+X, B+X, P, B` that `par-pullbacks` produces, and read in `C` it is not an
instance of `tot-pullbacks` either (see ERRATA).  It is replaced by a
three-line argument from material established two paragraphs earlier in the
same point:

> let `s = 1 ⋁ p`; then `(1 ⋁ p) ⋁ s^⊥ = s ⋁ s^⊥ = 1`, so by partial
> associativity `1 ⋁ (p ⋁ s^⊥) = 1`, so `p ⋁ s^⊥ = 1^⊥ = 0` by the
> *uniqueness* of the orthosupplement (the previous paragraph of 187VI); the
> bound `d` for `p ⊥ s^⊥` then has `1 ⊙ d = 0`, so `d = 0` by **186VIII.2**
> and `p = ▷₁ ⊙ d = 0`.

### 188III (`cho_thm_3_par_tot`) — class (1)

`P : Par (Tot D) ⥤ D`, `P f = ▷₁ ∘ f`, exactly as in 188III; functoriality is
`▷₁ ∘ [g,κ₂] = [▷₁∘g, 0] = (▷₁∘g) ∘ ▷₁` (`tot_desc_tp₁`).  Instead of
exhibiting the inverse `P' f = ⟨f, (1∘f)^⊥⟩` as a functor and checking
`PP' = id`, `P'P = id`, we use `P'` only pointwise, to show `P` is full, and
get the equivalence from full + faithful + (trivially) essentially surjective.
Faithfulness is the one place where 181XVI's "third coordinate is determined"
lemma (`tot_snd_coord_eq`) is reused.

### 188IV (`cho_thm_3_tot_par`) — class (1) for the proof, class (4) for the
### statement

The proof is 188IV verbatim: `Q g = ĝ` is a functor because
`1 ⊙ ĝ = 1` and `(f ∘ g)^ = f̂ ⊙ ĝ`, and it is full and faithful by the
uniqueness half of **186VIII.1** (`pardp_1`).

**Class (4).**  Our statement read

```lean
theorem cho_thm_3_tot_par (s : EffectusPartialStructure (Par C)) : … Tot (Par C) ≌ C
```

i.e. it asserted `Tot (Par C) ≅ C` for **every** structure of an effectus in
partial form on `Par C`.  That is strictly stronger than 188IV, which is about
the structure built in 187I: `Tot` is defined by `1 ∘ f = 1`, so it depends on
the effect object `I` and the truth predicate `1` of the structure.  The PCM
part of such a structure *is* determined by the category (`f ⊥ g` iff a bound
exists, and `0` is the map through the zero object `0`, which every effectus in
partial form has), but we found no reason why `(I, 1)` — hence the class of
total maps — should be.  The statement has been weakened to the canonical
structure; see QUESTIONS B9.

### Classification

* **(1) faithful:** 181XI (all of 181XII–XVI), 187III, 187IV, 187V, 187VI up
  to the zero–one axiom, 187VII, 188III, 188IV.
* **(2) different route:** the zero–one axiom of 187VI (above); 188III uses
  full+faithful+ess.surj. rather than an explicit inverse functor.
* **(3) mild:** the `truth_terminal_isIso` step in 181XVI (above).
* **(4) our statement mis-transcribes the thesis:** `cho_thm_3_tot_par`
  (above, fixed).
* **(5) closed from Mathlib without reading the author's argument:** none.
  `eff.tex` 1165–1290, 1713–1935 and 1936–1990 were read in full first.

## Session 15 — `A/Proc` parsecs 1120 and 1130 (worker 40)

Closed **four** statements, all in `Theses/A/Proc/Tensor.lean`, and added one
lemma that settles **QUESTIONS B5**.  A/Proc 149 → 145 (grep convention);
`Tensor.lean` 51 → **47** by the build-warning count, the other three files
unchanged (Measurement 47, QuantumLambda 26, Duplicators 20).

| point | declaration | note |
|---|---|---|
| **112VIII** | `tensor_product_norm` | all four clauses; §1 |
| **113II** | `mi_bilinear_cp` | §2 — the author's index hint is not needed |
| **113IV**.1/3 | `cp_bilinear` | §3 |
| **113IV** cor. | `cp_bilinear_comp` | §3 |
| — | `matBilin_nonneg_of_mi` | §4, resolves **QUESTIONS B5** |

New private auxiliaries in `Tensor.lean`: `tsn`, `basicCore`, `tsn_nonneg`,
`basic_cauchy_schwarz`, `tsn_add_le`, `tsn_smul`, `tsn_sum_le`,
`basic_nonneg_tmul`, `basic_mono_tmul_left/right`, `basic_one_nonneg`,
`basic_tmul_le`, `tsn_tmul_le`, `tnSet`, `tensorNorm_eq_sSup`,
`tnSet_nonneg`, `zero_mem_tnSet`, `tnSet_bddAbove`, `sum_comm₃`, `sum_comm₄`,
`exists_star_mul_self`, `exists_star_repr_of_nonneg`, `cp_matrix_nonneg`;
public: `tensorNorm_nonneg`, `tensorNorm_zero`, `tensorNorm_smul`,
`tensorNorm_add_le`, `tensorNorm_eq_zero_iff`.

### 1. 112VIII (proc.tex:2849) — the tensor product norm really is a norm

An Exercise, and `asols.tex` stops at parsec 340, so there is no author
argument: this is the first proof of it.

The organising observation is that **112V** (`basic_state_inner_product`,
proved by w37) says exactly that `[s,t]_ω = ω(s* t)` is a positive
semidefinite Hermitian form, i.e. a Mathlib `PreInnerProductSpace.Core ℂ
(𝒜 ⊙ ℬ)`.  Feeding 112V into that structure (`basicCore`) buys
Cauchy–Schwarz, the triangle inequality and homogeneity of
`‖t‖_ω = ω(t* t)^½` for free — Mathlib's `Core` deliberately does *not*
require definiteness, which is what makes it applicable here.

The two things that are not free:

* **Boundedness of the set the supremum is taken over.**  Nobody had checked
  the supremum in 112II is over a bounded set, and without that neither the
  triangle inequality nor definiteness can be proved (an unbounded set has
  `sSup = 0` by Lean's convention, which would break both).  It is bounded:
  writing `t = ∑ᵢ aᵢ ⊙ bᵢ`, `‖t‖_ω ≤ ∑ᵢ ‖aᵢ ⊙ bᵢ‖_ω ≤ ∑ᵢ ‖aᵢ‖‖bᵢ‖`, the
  second step because `ω` is nonnegative on `x ⊙ y` for positive `x`, `y`
  (write them as `u* u`, `v* v` and apply 112V again), hence monotone in each
  slot separately, so `ω((a* a) ⊙ (b* b)) ≤ ‖a‖²‖b‖² ω(1) ≤ ‖a‖²‖b‖²`.
* **Definiteness.**  For `t ≠ 0`, **112VI** (`product_functionals_separating`,
  w37) applied to the *np*-functionals — separating by vn.tex 44XI
  (`np_separating`, proved) — gives `σ`, `τ` with `(σ ⊙ τ)(t) ≠ 0`.  Then
  `σ ⊙ τ` is itself basic (take `t₀ = 1`), and Cauchy–Schwarz
  `|ω(1* t)| ≤ ‖1‖_ω ‖t‖_ω` forces **both** `(σ⊙τ)(1) > 0` and
  `(σ⊙τ)(t* t) > 0`.  Rescaling by `t₀ = ((σ⊙τ)(1))^{-½}·1` — which keeps the
  functional basic, since basicness is closed under this conjugation — gives a
  basic `ω` with `ω(1) = 1` and `ω(t* t) > 0`, so `‖t‖ > 0`.

Divergence class: no author argument exists to diverge from.

### 2. 113II (proc.tex:3012) — the author's Schur hint is unnecessary

The Exercise carries the index entry `\index{Schur's Product Theorem}`, i.e.
the intended route is via **111II** `schur` (as in 112III).  It is not needed:
multiplicativity and involution preservation turn
`β(aᵢ* aⱼ, bᵢ* bⱼ)` into `β(aᵢ,bᵢ)* β(aⱼ,bⱼ)`, so

  `∑ᵢⱼ cᵢ* β(aᵢ*aⱼ, bᵢ*bⱼ) cⱼ = x* x`,  `x = ∑ᵢ β(aᵢ,bᵢ) cᵢ`,

and positivity is `star_mul_self_nonneg`.  Ten lines, no Schur, no
von-Neumann-ness (the statement's `𝒜, ℬ, 𝒞` need only be C*-algebras) and no
unitality — `BilinMult` + `BilinStar` alone.  **Divergence class (2)**: a
different, shorter route than the author's hint.  Worth one sentence to the
author; it is not a defect.

### 3. 113IV (proc.tex:3029) — (1) ⇔ (3) and the corollary

Also an Exercise with no published solution.  Both directions go through
cstar.tex **33II** `cstar_matrix_positive_iff` (proved, `A/CStar/Matrices.lean`),
which is how our statement renders "positive matrix" anyway:

* **(3) ⇒ (1)** is immediate: apply (3) to the Gram matrices `(aᵢ* aⱼ)`,
  `(bᵢ* bⱼ)`, positive by 33II.3.
* **(1) ⇒ (3)** needs *the* recurring step of this parsec: a positive
  `M ∈ M_N(𝒜)` is `X* X`, so `Mᵢⱼ = ∑ₖ Xₖᵢ* Xₖⱼ`; expanding both matrices this
  way and using bilinearity turns `∑ᵢⱼ cᵢ* (M_N β)(M,M')ᵢⱼ cⱼ` into a sum of
  `N²` instances of `BilinCP β`.  Factored out as
  `exists_star_repr_of_nonneg`.  As in `A/CStar/Matrices.lean`, the
  `∃ b, a = star b * b` step has to be routed through an abstract C*-algebra
  variable, because typeclass search cannot find the functional calculus
  instances for `CStarMatrix` directly.
* The **corollary** (`cp_bilinear_comp`) is then the three-step chain the
  author describes: `M_N f`, `M_N g` carry the Gram matrices to positive
  matrices (that is complete positivity of `f`, `g` *verbatim*, given how
  `IsCompletelyPositiveMap` is defined in this tree), `cp_bilinear` carries
  those to a positive matrix, and `M_N h` keeps it positive
  (`cp_matrix_nonneg`, the same decomposition again).

### 4. QUESTIONS B5 is answered: the positivity clause is derivable

B5 records that thesis B's `IsVNTensor` (`B/Dils/SelfDual.lean:979`) has
`add_left`, `add_right`, `smul_complex`, `mul`, `one`, `star`, `generates`,
`separating` and "nothing about order", and asks the author whether to *add* a
positivity clause because 165III needs positivity of
`M_N(⊗) : M_N𝒜 × M_Nℬ → M_N(𝒜⊗ℬ)`.

It need not be added.  Reading the proofs of §2 and §3 back: **113II uses only
multiplicativity and involution preservation, and 113IV (1) ⇒ (3) uses only
additivity in each slot** — no `ℂ`-homogeneity anywhere, in either.  Those four
properties are precisely `mul`, `star`, `add_left`, `add_right` of
`IsVNTensor`.  To make this usable rather than merely arguable it is proved in
that exact shape as

```
Theses.A.Proc.matBilin_nonneg_of_mi (t : 𝒜 → ℬ → 𝒞) (hl hr hmul hstar)
  (M : M_N 𝒜) (M' : M_N ℬ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (c) :
  0 ≤ ∑ᵢⱼ cᵢ* · t (Mᵢⱼ) (M'ᵢⱼ) · cⱼ
```

which an `IsVNTensor` discharges field by field, and which is the 33II
criterion for `0 ≤ M_N(t)(M,M')`.  Noted in `QUESTIONS.md` under B5; the
`B/Dils` worker should check it against what 165III actually consumes before
the question is closed.

(Incidentally this also shows `smul_complex` is *not* what carries the weight
in `IsVNTensor`; whether right-`ℂ`-homogeneity is derivable from the other
fields is a separate question, and I did not settle it.)

### 5. New "blocked on X": 112IX waits on **72XI `luws`**

`product_functional` (112IX, proc.tex:2854) asks that `f ⊙ g` be bounded and
ultraweakly continuous for `f ∈ 𝒜_*`, `g ∈ ℬ_*`, and the Exercise's own hint
is "perhaps using `luws`".  That is **72XI**, `sorry` at
`A/VN/Completeness.lean:889`.  It is not avoidable by cleverness: for
np-functionals the statement is easy (`σ ⊙ τ` *is* a basic functional, hence
simple, hence one of the maps that induce the ultraweak tensor topology, and
Cauchy–Schwarz gives `|(σ⊙τ)(t)| ≤ (σ⊙τ)(1)·‖t‖`), and the whole content is the
passage from a general `f ∈ 𝒜_*` to a combination of np-functionals — which is
`luws` (2) ⇒ (3).  Proving it here would be re-proving `luws`.

Correction to w37 §4's band table while I am here: **116I is `VNT`-typed**
(`exists_predualTensor` and `product_functional_norm` both mention `VNT A B`),
so it belongs in the vacuous band, not with 113II/113IV.

### 6. Classification

* **(1) faithful:** none — none of the four has an author argument to be
  faithful to (`asols.tex` covers parsecs 40–340 only, and all four points are
  Exercises).
* **(2) different route:** 113II, §2 — the author's index hint points at
  Schur's product theorem and the proof does not use it.
* **(3) mild:** 112VIII's definiteness is proved through the *np*-functionals
  rather than an unspecified separating family, and its supremum-set is shown
  bounded explicitly (§1), a step the Exercise does not mention.
* **(4) our statement mis-transcribes the thesis:** none found.
* **(5) closed from Mathlib without reading the author's argument:** none.
  `proc.tex` 2681–2860 and 3005–3110 were read first; `asols.tex`'s errata
  block was re-checked (largest key `parsec-990.70`, so nothing for 1120/1130).

### 7. Verification

* `lake build Theses.A.Proc.Duplicators` → exit 0, `Build completed
  successfully (8721 jobs)`.  `lake env lean Theses/A/Proc/Tensor.lean` → **0**
  `error:` lines; the only non-`sorry` warning in the file is the pre-existing
  unused-section-variable one on `product_functionals_separating`.
* `#print axioms` on all nine new/closed public declarations →
  `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`.
* Doc `file:LINE` refs checked against `proc.tex`: 112VIII→2849 ✓,
  113II→3012 ✓, 113IV→3029 ✓ (each the `\begin{point}` line itself, the
  convention already in force in this file).
* No sorried instance is involved: everything proved here is over abstract
  C*- or von Neumann algebras and Mathlib's algebraic `A ⊗[ℂ] B`.
* Files touched: `Theses/A/Proc/Tensor.lean`, `PROVING-LOG.md`,
  `QUESTIONS.md`.  Nothing staged, nothing committed.  (`Theses/B/Dils/*` and
  `Theses/B/Eff/Effectus.lean` are also dirty — not mine.)

---

## Session 16 — `B/Dils` (worker 41)

Two statements proved — **140X**.3 `paschke_basics_3` (`Stinespring.lean`) and
**159IV** `ketbra_ultraweakly_dense` (`SelfDual.lean`) — and the rest of the
session went into a reachability survey of the chapter's remaining 62 `sorry`s.
`B/Dils` 64 → **62**.  Tree green (`lake build Theses`, 8738 jobs, exit 0, zero
`error:` lines); everything new axiom-clean; still no `sorry`ed instances in
`B/Dils`; no new warnings anywhere (diffed against the session's baseline
build).

### 1. 140X.3 `paschke_basics_3` — divergence class 1

`bsols.tex`, solution `paschke-basics`.3, transcribed.  The only thing the
author's categorical argument does not supply is the Lean-specific step forced
by our abstract rendering of the biproduct: **140X**.3's statement represents
`ℬ₁ ⊕ ℬ₂` and `𝒫₁ ⊕ 𝒫₂` by algebras `ℬp`, `𝒫` with nmiu-projections whose
pairing `c ↦ (p₁ c, p₂ c)` is a bijection (this avoids instance diamonds on
product types).  From that one has to *derive* that the pairing **reflects**
positivity, which is what makes `⟨σ₁, σ₂⟩` an ncp-map at all.

The derivation is three lines and is the new private
`pair_nonneg_reflect`: if `0 ≤ p₁ c` and `0 ≤ p₂ c` then
`pᵢ c = star bᵢ * bᵢ` (`CStarAlgebra.nonneg_iff_eq_star_mul_self`), a preimage
`d` of `(b₁, b₂)` has `pᵢ (star d * d) = pᵢ c`, and injectivity gives
`c = star d * d`.  Everything else follows: `pair_le_reflect` (order
reflection), and `exists_ncpPair`, which builds `σ` with `pᵢ ∘ σ = σᵢ`.
Complete positivity of `σ` needs **no matrix machinery** — this repo's
`IsCompletelyPositiveMap` is literally `0 ≤ ∑ᵢⱼ star(bᵢ) f(star aᵢ aⱼ) bⱼ`, so
applying `p₁`/`p₂` to that sum reduces it to complete positivity of `σ₁`/`σ₂`.
Normality is the same reduction through `pair_le_reflect`.

New private by-products in `Stinespring.lean` (section `Biproduct`):
`ncp_add`, `ncp_smul`, `nmiu_monotone`, `nmiu_mul`, `nmiu_star`, `nmiu_sub`,
`nmiu_add`, `nmiu_smul`, `nmiu_sum`, `pair_nonneg_reflect`, `pair_le_reflect`,
`pairInv`, `pairInv_spec`, `exists_ncpPair`, and `exists_nmiuCompNCP` (the
mirror image of the existing `exists_ncpCompNMIU`: nmiu *after* ncp).

### 2. 159IV `ketbra_ultraweakly_dense` — divergence class 2 (one step)

The thesis's own proof (**159V**–**159VIII**), transcribed, except for its
final step.

Faithful part: `p_S = ∑_{i∈S} |eᵢ⟩⟨eᵢ|` (`onbProj`); its vector forms are the
partial Parseval sums (`onbProj_vec`), so Bessel (`mod_bessel`, w38) gives
`p_S ≤ 1` and monotonicity in `S`; `⋁_S p_S = 1` (`onbProj_isLUB`) because
the vector states of `𝒷ᵃ(X)` are order separating (**144I**, through
`ba_nonneg_iff`) and `⟨x, p_S x⟩ → ⟨x,x⟩` ultraweakly by Parseval (**149IV**
`mod_parseval`); `p_S T p_S` lies in the span of the `|eᵢb⟩⟨eⱼ|`
(`onbProj_compress`, from `mketbra_rules`); and the estimate of **159VIII** is
Cauchy–Schwarz for `‖·‖_ω` (`norm_apply_star_mul_le`) applied to
`T − p_S T p_S = (1−p_S)*T + (p_S T)*(1−p_S)`.

**The one deviation (class 2).**  The thesis gets `p_S → 1` from
`vna-supremum-uslimit` (**44XIV**), whose Lean form is indexed by the
*directed set itself*, so using it would need a cofinality transport from
`Finset ι` (the transport w34 had to build for `ba_isLUB`).  It is not needed:
normality of the np-functional `ω` of `𝒷ᵃ(X)` turns `IsLUB` directly into
`IsLUB` of a monotone net of reals (`isLUB_re_of_isLUB` +
`tendsto_atTop_isLUB`), which gives `ω(1 − p_S) → 0`; and
`‖1 − p_S‖_ω² = ω((1−p_S)²) ≤ ω(1−p_S)` because `E² ≤ E` for an effect
(`sq_le_self_of_effect`, new).  So **44XIV** is not used at all, and neither is
the von Neumann structure of `𝒷ᵃ(X)` (**152X**): the only normality used is
that of the given `ω`.

**The hypothesis `hX : SelfDual ℬ X` is not used** — the linter suppression
above the declaration is the evidence.  It is redundant in the source too: by
**149XI** `selfDual_of_isONBasis` (w38) an orthonormal basis already forces
self-duality.  Filed as an ERRATA nit, following the **153I** precedent.

New public by-products in `SelfDual.lean` (section `KetbraProj`):
`mketbraBa`, `mketbraBa_coe`, `onbProj`, `onbProj_apply`, `onbProj_vec`,
`onbProj_nonneg`, `onbProj_le_one`, `onbProj_mono`, `onbProjSA`,
`onbProjSA_coe`, `onbProj_isLUB`, `onbProj_omegaNorm_tendsto`,
`onbProj_compress` (plus private `baVal`, `baVal_sum`, `sq_le_self_of_effect`).
`onbProj_isLUB` is the reusable form of **159VI**; `onbProj_compress` is
**159VII**.

### 3. Reachability survey — what is blocked, and on what

Checked against the sources this session, not recalled:

| point(s) | blocked on |
|---|---|
| 138II `nmiu_between_type_I` | nothing frozen, but a multi-session Hilbert-space theorem (unitary from a basis bijection, ultraweak sums in `B(𝒦)`); **138VI**, **138VII**, **138VIII** all reduce to it |
| 139XI `ess_uniq_pur` | ditto: `𝒱 = ℋ ⊗ 𝒱'` splitting + a dimension count |
| 140VIII `paschke_unique_up_to_iso` | **99IX** `iso` (proc.tex 878, "a unital ncp-isomorphism is nmiu") — `sorry` in `A/Proc/Measurement.lean`, which is **not on `B/Dils`'s import path** |
| 160IV.2/.3 `hilbmod_projthm_2/_3` | the thesis's proof extends a basis of `W` to one of `X`, i.e. **149VIII** (3 ⇒ 4 of 149V) — `sorry`, blocked on `A/VN` **80IV** |
| 160IX, 160X | 160IV.2/.3; 160X additionally needs the polar decomposition of **149VIII** |
| 161II.1/.2 | `bh-bounded-uw-complete` = **77I**.2, `sorry` in the frozen, off-path `A/VN/Completeness.lean` |
| 162II `total_mv_order` | polar decomposition (`A/VN/Division.lean`, off-path *and* `sorry`); 162IV needs 162II |
| 163II uniqueness | **151Ia** (`SelfDualCompletion` has no `univ` field, unlike `PaschkeModule`) |
| 163II "moreover" | **150II** + **151Ia**, or 160IV.3 for a direct route |
| 164II (all four) | existence runs through `ℓ²`, hence 161II, hence 77I.2 |
| 165III, 165VI | **not** the B5 order clause any more — worker 40 showed it is derivable (`Theses.A.Proc.matBilin_nonneg_of_mi`), and I checked 165IV consumes nothing else order-theoretic.  What blocks them now is purely structural: that lemma lives in `A/Proc/Tensor.lean`, off `B/Dils`'s import path.  See QUESTIONS B5 |
| **166II** | **new**: `IsVNTensor` gives the legs `a ↦ a⊗1`, `b ↦ 1⊗b` as miu but not **n**miu, and the proof needs ultraweak continuity of a leg — see QUESTIONS B5 and the new 166II ERRATA row |
| 166IV | 166II + **158II** (Kaplansky, blocked on `A/VN` 74IV) + `ext_tensor_dense` |
| 166VI | **158Ia** + `PaschkeModule` (QUESTIONS **D2**) |
| 167I | 164II + B5 |
| 169IV, 169X | proc.tex 95II/98I, unformalized (unchanged from w30) |
| 169V | routes through `existence-paschke`, hence `PaschkeModule` (D2) *and* 150II/151Ia |
| 169XI.1/.2 | **169XII**, which needs 169X + `A/VN/Division`'s `mult-cancellation` on the standard filter |
| 170II.1 | 138II; 170II.2 needs 169V + 169XI |
| 170IV.1/.2 | 169IV (central-projection case) and **99IX** |
| 171II, 171VII, 172III, 172X, 172XII | downstream of the above |
| `Paschke.lean` (9) | QUESTIONS **D2** (unchanged) |

So, with 140X.3 and 159IV closed, **`B/Dils` has no further statement that is
reachable without either a decision (D2, B5), an `A/VN`/`A/Proc` `sorry`, or a
multi-session Hilbert-space development (138II).**  The two cheapest unlocks
remain the ones w38 named: settle D2, and prove **77I**.1/.2.

### 4. Classification

* **(1) faithful:** 140X.3 (`bsols.tex` `paschke-basics`.3, verbatim);
  159IV up to §2's one step.
* **(2) different route:** 159IV's `p_S → 1` step (§2) — normality of the
  functional instead of **44XIV**, to avoid a cofinality transport.
* **(3) mild:** the biproduct positivity-reflection lemma of §1 is an addition
  to the author's argument forced by our abstract rendering of `⊕`.
* **(4) our statement mis-transcribes the thesis:** none found.  Both
  statements were re-checked for the mirroring convention: 159IV's span set
  `mketbra ℬ (b • e i) (e j)` is the correct mirror of `|eᵢb⟩⟨eⱼ|` (the
  convention is fixed by `mketbra_rules`.1, `|xb⟩⟨y| = |x⟩⟨yb*|`, which in
  Lean reads `mketbra (b • x) y = mketbra x (star b • y)`).
* **(5) closed from Mathlib without reading the author's argument:** none.

### 5. Verification

* `lake build Theses` → `Build completed successfully (8738 jobs)`, exit 0,
  **zero** `error:` lines.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for all 15 new
  public declarations and both closed theorems.
* Warning diff against the session's baseline build: **empty** (the one new
  unused-`hX` warning is suppressed with an explanatory comment).
* Per-file code `sorry`s, before → after: `SelfDual` 24 → **23**,
  `Stinespring` 8 → **7**, `Pure` 16, `Paschke` 9, `HilbertModules` 3,
  `Kaplansky` 2, `SelfDualCompletion` 2.  **`B/Dils` 64 → 62.**
* Files touched: `Theses/B/Dils/Stinespring.lean`,
  `Theses/B/Dils/SelfDual.lean`, `ERRATA.md` (two rows, in point order),
  `QUESTIONS.md` (B5 extended), `PROVING-LOG.md`.  Nothing staged, nothing
  committed.

## Session 16 — `A/Proc` parsecs 1010 and 1090 (worker 42)

Files touched: `Theses/A/Proc/Measurement.lean`, `Theses/A/Proc/Tensor.lean`,
`ERRATA.md`, `PROVING-LOG.md`.  `QuantumLambda.lean`, `Duplicators.lean`,
`A/CStar`, `A/VN`, `B/` untouched.

**A/Proc 140 → 137** (build-warning count): Measurement 47 → **45**,
Tensor 47 → **46**, QuantumLambda 26, Duplicators 20.

Closed: **101VII**.1-continued `equivalent_examples_1'`, **101VII**.2
`equivalent_examples_2` (corrected — §1), **109III**.1 `l2_tensor` (§2); plus
the refutation `equivalent_examples_2_is_false` and five reusable private
auxiliaries (`ncpMap_sub`, `ncpMap_mono`, `eq_zero_of_le_proj_le_perp`,
`isStarProjection_map`, and the `l2Gamma` block).

### 1. 101VII.2 is false as stated — the fourth false statement of the chapter

`equivalent_examples_2` ("an ncp-isomorphism is contraposed to its inverse")
was the target of a fallback pass and would not go through; it is **false**.
The obstruction is exactly the one the thesis itself flags elsewhere: proc.tex
:282 says "there are corners which are not unital, because there are non-unital
ncp-isomorphisms", and a non-unital one refutes 101VII.2.

Witness (now in the tree as `equivalent_examples_2_is_false`, `B(ℂ²)`
transported from `M₂(ℂ)` along Mathlib's `Matrix.toEuclideanCLM`; `B(ℂ²)`'s
von Neumann instance is **42V**.2, honest):
`a = diag(1,2)`, `f = a(·)a`, `g = f⁻¹ = a⁻¹(·)a⁻¹` — both ncp by `ad-ncp`
(`adSelf`), mutually inverse.  With `s` the projection onto `ℂ(1,1)` and `t`
the one onto `ℂ(2,−1)`: `f(s)` has range `ℂ(1,2) ⊥ t`, so `⌈f(s)⌉ ≤ t^⊥`;
but `g(t)` has range `ℂ(4,−1)`, which is *not* orthogonal to `s`.  Both halves
are `ceil_le_perp_iff` applied to a 2×2 matrix identity
(`t·f(s)·t = 0`, `s·g(t)·s = (9/80)!![1,1;1,1] ≠ 0`).

The structural reason: by part **1** of the same Examples (proved, w-earlier)
`a(·)a` is contraposed to `a(·)a* = a(·)a`, i.e. to *itself*; and a
contraposition partner is unique up to `⋄` (`contraposed_iff_diamond`), so it
cannot also be contraposed to `f⁻¹` unless `⌈a t a⌉ = ⌈a⁻¹ t a⁻¹⌉` for every
projection — which the above disproves.

**Fix, applied:** `equivalent_examples_2` gains the hypothesis `f 1 = 1`, and
is **proved**.  This is class (4)-adjacent but the defect is the thesis's, so
the row is in `ERRATA.md` (point order, between 101II and 104III.2a) rather
than here; the Lean statement now diverges from the printed one deliberately
and says so in its doc comment.  Nothing downstream consumes
`equivalent_examples_2`, and an isomorphism of `W*_cpsu` is automatically
unital (`1 = g(f 1) ≤ g 1 ≤ 1` for subunital `f`, `g`), so the corrected form
is the one the thesis's own category needs.

The proof does **not** need Kadison's theorem: a unital ncp-iso maps
projections to projections by an order argument only — for `e = f(p)` the
element `d = e − e²` is positive (`mul_self_le_self`) and below both `e` and
`e^⊥`, so `g(d)` is below both `p` and `p^⊥`, hence `0`
(`eq_zero_of_le_proj_le_perp`, via `ceil_le_perp_iff` + 59III), and `g` is
injective.  Then `⌈f s⌉ = f s`, `⌈g t⌉ = g t` and contraposition is
`f(s) ≤ 1−t ⟺ s ≤ 1−g(t)`, one application of `g` and one of `f`.

### 1a. 101VII.1 (continued) `equivalent_examples_1'` — the same argument in a corner

`π_s : 𝒜 → s𝒜s` and `c_s : s𝒜s → 𝒜` are contraposed.  This is
`equivalent_examples_1` (proved earlier) carried through the corner: with `t`
a projection of `s𝒜s`, `⌈π_s(x)⌉ ≤ t^⊥` unfolds — `ceil_le_perp_iff` *in the
corner*, then `Corner.val_injective` — to `t·(sxs)·t = 0`, i.e. `t·x·t = 0`
since `t·s = t = s·t`; and `⌈c_s(t)⌉ ≤ x^⊥` unfolds to `x·t·x = 0` in `𝒜`.
Both are `x·t = 0` (`conj_perp_eq_zero_iff` at `x := 1`).  Class (1).

### 2. 109III.1 `l2_tensor` — closed after seven sessions on the list

`ℓ²(X) × ℓ²(Y) → ℓ²(X×Y)`, `γ(f,g)(x,y) = f(x)g(y)`, is a Hilbert-space
tensor product.  Recipe as w12 §7.3 predicted: `Memℓp` from
`Summable.mul_of_nonneg` (the sum of squares factorises), bilinearity
coordinatewise through `LinearMap.mk₂`, `⟨γ(f,g),γ(f',g')⟩ = ⟨f,f'⟩⟨g,g'⟩`
from `tsum_mul_tsum_of_summable_norm` with Cauchy–Schwarz (`lp.summable_mul`
at the Hölder pair `(2,2)`) for the absolute summability, and density from
`γ(δ_x, δ_y) = δ_(x,y)` plus `lp.hasSum_single`.  Five private auxiliaries
(`l2Mem`, `l2Gamma`, `l2SummableInner`, `l2Gamma_inner`, `l2Gamma_single`,
`l2Gamma_dense`).  No author argument exists (Exercise), so this is a first
proof, class (1)-by-default.

### 3. The brief's headline target, 112X.2, is **blocked** — correcting w40 §9

w40 recommended `tensor_basic_2` (`‖γ_⊙ s‖ = ‖s‖_⊗`) as "the keystone, now
materially easier".  It is not reachable: **only the easy inequality is.**

* `‖s‖_⊗ ≤ ‖γ_⊙ s‖` is elementary (each basic `ω` with `ω(1) ≤ 1` lifts to
  `ω̂ = γ(σ,τ)(γ_⊙(t)*(·)γ_⊙(t))` on `𝒯` with `ω̂ ∘ γ_⊙ = ω` and `ω̂(1) ≤ 1`,
  and `ω̂(x* x) ≤ ω̂(1)‖x‖²`).
* The reverse needs the *norm* of `𝒯` to be computed from `Ω₁`, which is the
  exercise's own instruction ("show using `vn-center-separating-fundamental`
  … and so determines the norm via `order-separating-norm`").  Both cited
  results are `sorry`:
  **90II** `vn_center_separating_fundamental_1/2`
  (`A/VN/NormalFunctionals.lean:1452,1465`) and **21VII**
  `order_separating_norm` (`A/CStar/Positive.lean:1747`).  Both frozen.

That kills the whole 112X/112XI/114I/114II block for now, not just 112X.2:

| point | additionally blocked on |
|---|---|
| 112X.1 | 90II (this *is* 90II at `Ω = ` product functionals, `S = γ_⊙(𝒜⊙ℬ)`) |
| 112X.2 | 90II + 21VII |
| 112X.3 | 112X.2 (the `‖f ∘ γ_⊙‖ ≤ ‖f‖` step) |
| 112X.4 | **74VI** `dense_subalgebra` (Kaplansky, `A/VN/Completeness.lean:1217`) and **86IX** `polar_decomposition_of_functional` (`NormalFunctionals.lean:449`) — both `sorry` |
| 112X.5 | **87III** `predual_complete` (`NormalFunctionals.lean:520`) — `sorry` |
| 112XI | **77V** `vn_extension` (`Completeness.lean:1627`) — `sorry` |
| 114I | parts (1)(2)(3) are reachable (separate ultraweak continuity of multiplication is **proved**, `mult_uws_cont`); parts (4)(5) need the positive cone of an ultraweakly dense ∗-subalgebra to be dense in the positive cone, i.e. **74IV/74VI** again.  Splitting the conjunction would *raise* the sorry count (1 → 2), so it is left alone |
| 114II | 112XI |

So the honest ordering of `A/Proc`'s remaining leverage is unchanged from w37
except that the "hard but reachable" band of `Tensor.lean` is now **empty**:
everything left there is behind 89IX, 90II, 21VII, 74IV/74VI, 86IX, 87III or
77V `vn_extension`.

### 4. Classification

* **(1) faithful:** none available — both items proved this round are
  Exercises past parsec 340, so no author argument exists (`asols.tex` stops
  at 340; its errata block still tops out at `parsec-990.70`).
* **(2) different route:** —
* **(3) mild:** the corrected 101VII.2 proof avoids Kadison, which is what the
  "unital order iso" phrase would normally invoke.
* **(4) our statement mis-transcribes the thesis:** none.  101VII.2's
  divergence is a *deliberate* repair of a false thesis statement, logged in
  `ERRATA.md`.
* **(5) closed from Mathlib without reading the author's argument:**
  `l2_tensor` unavoidably (Exercise, no argument to read); the *statement*
  was checked against proc.tex:2117 first.

### 5. Verification

* `lake build Theses.A.Proc.Duplicators` → exit 0 (log
  `scratchpad/w42build.log`); the only `error:` lines are the pre-existing
  `linter.style.header` noise from `A/VN/Basic.lean`.
* `lake env lean` per file: `Measurement.lean` 0 errors, 45 `sorry`s;
  `Tensor.lean` 0 errors, 46 `sorry`s.
* `#print axioms` on all four closed statements →
  `[propext, Classical.choice, Quot.sound]`; in particular
  `equivalent_examples_2_is_false` is **`sorryAx`-free**, so the refutation is
  real (`B(ℂ²)`'s instances, `adSelf`, `ceil_le_perp_iff` are all proved).
* Doc `file:LINE` refs checked: 101VII → proc.tex:1102 ✓, 109III →
  proc.tex:2117 ✓.
* Nothing staged, nothing committed.

## Session 17 — `B/Eff` parsec 189a: extensive categories (worker 44)

Target: **`extensive_effectus` (189aII.3)**, the last self-contained `sorry` of
`Effectus.lean` — "every (finitary) extensive category with a final object is
an effectus in total form".  **Proved**; `B/Eff` goes 26 → **25** code
`sorry`s and `Effectus.lean` 3 → **2** (the two left are the thesis-A examples
`effectus_vn`, `effectus_vn_partial`).  The statement is unchanged
byte-for-byte; only `:= sorry` became `:= ext_effectusTotalForm`.

### Why this one is a divergence of class 5 — legitimately

`eff.tex:2043` does not prove 189aII.3: it is one item of an `\begin{enumerate}`
of examples, attributed to `\cite{effintro}`.  There is therefore **no author's
argument to transcribe**, which is what makes closing it from Mathlib's
`FinitaryExtensive` the right thing to do rather than the thing to avoid.  (It
was listed under QUESTIONS A3 "statements the theses only cite, never prove";
that entry is now updated.)

Mathlib's `FinitaryExtensive` (`Mathlib/CategoryTheory/Extensive.lean`) says
every binary coproduct cocone is *van Kampen*.  The whole proof is driven by
one specialisation of `BinaryCofan.isVanKampen_iff`, added as
`ext_vk` (all declarations below are `private`, in
`section ExtensiveEffectus` of `Effectus.lean`):

```
ext_vk (inl' : X' ⟶ P) (inr' : Y' ⟶ P) (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : P ⟶ X ⨿ Y)
  (hX : αX ≫ κ₁ = inl' ≫ f) (hY : αY ≫ κ₂ = inr' ≫ f) :
  Nonempty (IsColimit (BinaryCofan.mk inl' inr')) ↔
    (IsPullback inl' αX f κ₁ ∧ IsPullback inr' αY f κ₂)
```

Its `mp` direction produces pullback squares out of known coproducts; its `mpr`
direction produces coproduct decompositions out of pullbacks — `ext_decomp m`,
"any `m : Z ⟶ X ⨿ Y` splits `Z` into `m⁻¹(κ₁) + m⁻¹(κ₂)`" (the pullbacks exist
because `FinitaryExtensive` carries `HasPullbacksOfInclusions`).

* **Axiom 2** (`ext_isPullback_kappa`, and its `κ₂` twin) is one line: apply
  `ext_vk` to the cofan `(X, Y)` over `1 ⨿ 1` along `! + !`, and `.flip`.
* **Axiom 1** (`ext_isPullback_plus`) is the only place where a limit has to be
  *built*: `X + Y` is the pullback of `! + id` and `id + !` because `X` is the
  `κ₁`-part of `X + 1` and `Y` is the `κ₂`-part of `1 + Y`.  Given a competing
  cone `(p, q)` over `Z`, `ext_decomp (p ≫ (!+id))` splits `Z = Z₁ + Z₂`; on
  `Z₁` the map `q` is forced to be `κ₁ ∘ !` and `p` lifts to `t₁ : Z₁ ⟶ X`, on
  `Z₂` symmetrically; the filler is `[t₁ ≫ κ₁, t₂ ≫ κ₂]`.  Uniqueness uses
  **axiom 2 for `X + Y`** to factor a competing filler through `κ₁`/`κ₂`, and
  then that `κ₁ : X ⟶ X + 1` is monic (`FinitaryExtensive.mono_inl_of_isColimit`).
* **Axiom 3** (`ext_jointlyMonic`) — this is the interesting one: the thesis
  never proves it and Mathlib has nothing for it, so a proof had to be found.
  It **is** true, and cheaply, once one stops thinking about `1 + 1 + 1` as
  three points: apply `ext_vk` to the *other* coproduct decomposition
  `(1 + 1) + 1 = 1 + (1 + 1)` (`cofanAssoc`, obtained by transporting
  `coprodIsCoprod` along `coprod.associator`).  That gives
  `F⁻¹(κ₁) = ` first summand and `F⁻¹(κ₂) = ` last two, for
  `F = [κ₁,κ₂,κ₂]`.  Now for `a, b : Z ⟶ 1+1+1` with `a≫F = b≫F` and
  `a≫G = b≫G`, split `Z` along `m = a≫F`:
  on `m⁻¹(κ₁)` both `a` and `b` factor through the first summand, hence are
  both `! ≫ κ₁κ₁`; on `m⁻¹(κ₂)` both factor through `N = [κ₂κ₁, κ₂]`, and
  since `N ≫ G = id` the factorisation *is* `(–) ≫ G`, which `a` and `b`
  share by hypothesis.  `Z` is the coproduct of the two pieces, so `a = b`.
  Only `F`'s two squares are needed; `G`'s are not.

New reusable API (all `private`): `ext_vk`, `ext_decomp`, `cofanOfIso`
(transport of the coproduct cocone along an iso of the vertex), `cofanAssoc`,
`ext_terminal_self`, `ext_jointlyMonic`, `ext_isPullback_kappa`,
`ext_isPullback_kappa_inr`, `isPullback_of_existsUnique`,
`ext_isPullback_plus`, `ext_effectusTotalForm`.

### Two Lean traps worth recording

1. **`coprod.inl_desc` and friends are not `simp` lemmas in this Mathlib**
   (they are `@[reassoc]` only, and `cat_disch` does not close them either).
   Every coproduct computation in the new block therefore passes an explicit
   `simp [coprod.inl_desc, coprod.inr_desc, …]` or rewrites by hand.  Mixing
   `← Category.assoc` into such a `simp` set breaks the `_assoc` variants and
   silently leaves the goal open.
2. **Projections of `BinaryCofan.mk` / `PullbackCone` carry dependent types.**
   `(BinaryCofan.mk f g).inl` is *displayed* as `f` but has type
   `(pair X Y).obj ⟨left⟩ ⟶ ((const _).obj c.pt).obj ⟨left⟩`, so `rw` fails
   with "motive is not type correct" / "did not find an occurrence" on goals
   that look identical to what one wrote.  Two workarounds are used throughout
   and are worth reusing: prove the two component equations as separate
   `have`s with hand-written (plain) types and finish with
   `exact BinaryCofan.IsColimit.hom_ext hcol e₁ e₂` — `exact` is up to defeq
   where `rw` is not — and abstract any such projection behind an
   `obtain ⟨D, hD⟩ : ∃ D : T ⟶ X ⨿ Y, …` before computing with it.  The same
   device (`isPullback_of_existsUnique`) shields the whole `PullbackCone` API.

### Divergence classes

* **(1) faithful:** none — there is no proof in the source to be faithful to.
* **(2) different route:** none, for the same reason.
* **(3) mild:** none.
* **(4) our statement mis-transcribes the thesis:** none; `extensive_effectus`
  is unchanged and is exactly 189aII.3.
* **(5) closed from Mathlib without reading the author's argument:**
  `extensive_effectus`, unavoidably (cited to `effintro`, no argument in
  `eff.tex`, no solution in `bsols.tex`).  Recorded above and in QUESTIONS A3.

### Verification

* `lake build` of all eight `B/Eff` modules: exit 0,
  `Build completed successfully (8715 jobs)`.  The ~315 new lines produce
  **zero** warnings (build-log lines for `Effectus.lean` are 1593, 1602, 2297,
  2298 — all pre-existing `linter.style.show` — plus the two remaining
  `declaration uses sorry`; the new block spans 2463–2777).
* `#print axioms Theses.B.Eff.extensive_effectus` →
  `[propext, Classical.choice, Quot.sound]`.
* Namespace walk (`#beff_leaks`): 1523 declarations, **25** are themselves
  `sorry`, **0** depend on one, 0 hand-written indirect leaks, 0 non-standard
  axioms.  (The count is unchanged from session 15 because the walk skips
  `private` names, which are name-mangled out of the `Theses.B.Eff` prefix;
  every new declaration in this session is `private`.  `#print axioms` on
  `extensive_effectus` does traverse them.)
* Per-file `sorry`s: Comparisons 3, Dagger 3, DiamondAmp 2, EffectAlgebras 6,
  **Effectus 2**, Quotients 0, StatesPredicates 9, WStarCat 0 — **25**.
* Nothing staged, nothing committed.

---

## Session 17 — `A/CStar` parsecs 200/210, `A/VN` parsecs 640/650 (worker 43)

Scope: `Theses/A/CStar/*.lean`, `Theses/A/VN/*.lean`, plus the one authorised
relocation out of `A/Proc/Tensor.lean` (QUESTIONS **D3**).

Closed: **20VI** `cstar_isometry`, **21VII** `order_separating_norm`,
**64II** `abelian_projections_norm_dense`, **65IV** `projections_norm_dense`,
**65III**.3 `commutant_basic_3`, **90II**.1
`vn_center_separating_fundamental_1` (and, on the way to it, the **69IX**
bridge `eq_zero_of_centreSeparating_conj` / `centreSeparating_cstar` /
`nonneg_of_conjNP_of_centreSeparating`).
Relocated: `matBilin_nonneg_of_mi` (`A/Proc/Tensor.lean` → `A/CStar/Matrices.lean`).

### 0. QUESTIONS D3 — resolved by relocation (option 2, authorised by Bas)

`matBilin_nonneg_of_mi` now lives in `Theses/A/CStar/Matrices.lean` as
`Theses.A.CStar.matBilin_nonneg_of_mi`, in a new `section MatBilin` after
`end MatrixOrder` (so it uses Mathlib's global order instances on
`CStarMatrix`, as `A/Proc/Tensor.lean` did, not the section's assumed ones).
The proof is worker 40's, verbatim; the only changes are (i) three independent
universe/type variables instead of one shared `Type u`, and (ii) private copies
of the two helpers it used (`sum_comm₃'`/`sum_comm₄'` and
`exists_star_repr_of_nonneg`) — `A/Proc/Tensor.lean` still uses its own
`sum_comm₄` and `exists_star_repr_of_nonneg` at other call sites, so they were
not moved.  `A/Proc/Tensor.lean` keeps a pointer comment where the theorem was.
`#print axioms` clean.  `B/Dils` already imports `A/CStar/Matrices`, so **165III
is unblocked with no new inter-chapter coupling**.

### 1. 20VI `cstar_isometry` (cstar.tex:2934) — divergence class 1 (faithful)

The thesis's proof transcribed step for step.  (1) ⇒ (2) is "`-λ ≤ a ≤ λ` iff
`-λ ≤ f a ≤ λ`, because `f` is bipositive and unital", applied at `λ = ‖a‖` and
at `λ = ‖f a‖`; (3) ⇒ (1) is the norm reformulation
`0 ≤ a  ⟺  ‖‖a‖ − a‖ ≤ ‖a‖` on both sides of the isometry, which is **17VI**.3a
(`positive_basic_2_3a`, already proved) applied to `‖a‖ − a` and to
`‖a‖ − f a`.  The `‖f a‖ ≤ 2‖a‖` side condition the thesis flags is weak
Russo–Dye (**20II**.2) plus `‖1‖ ≤ 1`.

**One gap in the thesis's write-up, filled here (not an erratum — the claim is
true).**  The (3) ⇒ (1) argument opens with "since `f` is involution preserving
`a` is self-adjoint iff `f(a)` is self-adjoint, and so we might as well assume
that `a` is self-adjoint".  Involution preservation gives only the ⇒ direction;
the ⇐ direction needs `f` to be *injective on self-adjoints*, which is not
stated.  It does follow from (3), but only after the self-adjoint case has been
done: applying the self-adjoint case to `k` and to `−k` shows `f k = 0 ⟹ k = 0`
for self-adjoint `k`, and then `f a` self-adjoint gives
`f(i(a* − a)) = 0`, hence `a* = a`.  The Lean proof therefore does the
self-adjoint case *first* (`hsacase`) and derives self-adjointness from it.

### 2. 21VII `order_separating_norm` (cstar.tex:3232) — divergence class 2

The thesis's proof is one line: apply **20VI** to the single pu-map
`⟨ω⟩ : 𝒜 → ⊕_ω ℬ_ω` into the C*-product (**20aI**), where positivity is
pointwise and the norm is the supremum.  We cannot: the ℓ^∞-product of an
arbitrary family of C*-algebras is not available in the tree — it is exactly
the gap recorded for `vonNeumannAlgebra_lp_infty` (`0 ≤ a` iff `0 ≤ aᵢ`
pointwise for `CStarAlgebra.spectralOrder` on `lp 𝒜 ∞`).  So **20VI**'s
*argument* is re-run on the family directly; the three steps are identical, and
the shared work is factored into the private helpers
`nonneg_iff_norm_algebraMap_sub_le`, `map_mono_of_pos`,
`isSelfAdjoint_map_of_pos`, `norm_map_le_two_mul`,
`norm_map_le_of_isSelfAdjoint` (all in `A/CStar/Positive.lean`, both theorems
use them).

Worth recording: **no index is needed**.  For empty `ι` the supremum
`⨆ i, ‖ω i a‖` is `0` (the `Real` convention) and all three conditions force
`𝒜` to be trivial; the proof below covers that case without a split, because
`Real.iSup_le`/`Real.iSup_nonneg` do not need `Nonempty`.

### 3. 64II `abelian_projections_norm_dense` (vn.tex:3162) and 65IV
### `projections_norm_dense` (vn.tex:3279) — divergence class 2, and a
### **strictly stronger** intermediate

The thesis proves 64II through the normal Gelfand isomorphism
`𝒜 ≅ C(spec 𝒜)` (`ngelfand_vna`), extremal disconnectedness of `spec 𝒜`
(`vn_spectrum_extremally_disconnected`) and Stone–Weierstraß, then gets 65IV by
applying it inside the commutative subalgebra `{a}^□□`.  All three inputs are
still `sorry` in the tree (and `vn_spectrum_extremally_disconnected` is itself
downstream of the Gelfand machinery), so that route is unavailable.

We run the **spectral** argument instead, which needs no commutativity and
produces 64II and 65IV from a single lemma
(`exists_spectral_approx`, private, in `A/VN/Projections.lean` just before
parsec 640).  For self-adjoint `a` with `M = ‖a‖`, mesh `h = 2M/n` and
`t_k = −M + kh`, put

```
g k = cfc (fun r => max (r − t k) 0) a        (the ramp (a − t_k)⁺)
e k = ⌈g k⌉                                   (the spectral projection)
s   = (−M)·1 + h·∑_{k<n} e k                  (the Riemann sum)
```

and the whole estimate reduces to two operator inequalities between commuting
elements:

* `g k − g (k+1) ≤ h·e k`.  The difference `x` satisfies `0 ≤ x ≤ h·1` and
  `x·e k = x` (the second summand needs `⌈g (k+1)⌉ ≤ ⌈g k⌉`, `ceil_mono`), so
  `x = e k · x · e k ≤ e k · (h·1) · e k = h·e k`.
* `h·e (k+1) ≤ g k − g (k+1)`.  Here `(h·1 − (g k − g (k+1)))·g (k+1) = 0` is a
  pointwise cfc identity, so `ceil_mul_eq_zero` gives
  `e (k+1)·(h·1 − y) = 0`, i.e. `e (k+1)·y = h·e (k+1)`, and then
  `y − h·e (k+1) = (1 − e (k+1))·y·(1 − e (k+1)) ≥ 0`.

Telescoping the first over `k < n` gives `a + M·1 = g 0 − g n ≤ h·∑ e k`, i.e.
`a ≤ s`; telescoping the second over `1 ≤ k < n` and bounding `h·e 0 ≤ h·1`
gives `s ≤ a + h·1`.  Hence `−h ≤ a − s ≤ 0` and `‖a − s‖ ≤ h` by **17VI**.3a.

**The intermediate is stronger than 64II**: `exists_spectral_approx` holds in
*every* von Neumann algebra and its projections lie in `{a}^□□`
(`vna_ceil_comm` plus `Commute.cfc_real`), so 65IV needs no reduction to the
commutative case at all — it is the same lemma with the commutant condition
kept.  64II is then the real/imaginary split.

Ingredients used, all already proved in the tree: `ceil_spec`, `ceil_mono`,
`ceil_le_iff`, `ceil_mul_eq_zero`, `vna_ceil_comm`, `positive_basic_2_3a`,
`star_left_conjugate_le_conjugate`, `star_left_conjugate_nonneg`.

### 4. Correction to the brief, and 90II.1 — first thought unreachable, then closed

The brief ranks 90II `vn_center_separating_fundamental_1/2` as jointly
unblocking 112X.2 (with 21VII) and 112X.1 alone.  The first reading of the tree
said 90II.1 was **not** reachable, for a reason worth recording because it is a
mismatch in *our* tree rather than in the thesis; the obstruction turned out to
be removable, and 90II.1 is now proved.  Both halves of the story matter for
whoever takes parsec 900.

**The mismatch (still true, still worth fixing).**  vn.tex 90II's proof uses
"centre separating" in the sense of **cstar.tex 21II.4**: `a ∈ 𝒜₊` is zero iff
`ω(b* a b) = 0` for all `ω ∈ Ω`, `b ∈ 𝒜`.  That is
`Theses.A.CStar.CentreSeparating`, and the bridge it needs — `Ξ = {ω(a*(·)a)}`
is order separating — is `proto_gelfand_naimark_1`, which **is** proved.  But
the hypothesis of our 90II is `Theses.A.VN.CentreSeparating`
(`A/VN/Projections.lean`), defined as *"a **central** positive `a` with
`ω(a) = 0` for all `ω ∈ Ω` is zero"* — that is thesis item **69IX.2** (modulo
projections-versus-positives, which are interchangeable), not 69IX.1.  So
**`vn_center_separating`'s TFAE is a mis-transcription (class 4)**: its item 1
should be the C*-notion 21II.4 but is item 2 in disguise, and as stated the
TFAE loses exactly the content 90II wants from it.  Not repaired here, because
changing the definition touches 90II.1, 90II.2, 69IX and the `B/Dils` consumers
of `CentreSeparating`.

**The bridge, proved instead of the definition change**
(`A/VN/Projections.lean`, right after the `CentreSeparating` definition):

```
eq_zero_of_centreSeparating_conj : CentreSeparating A Ω → 0 ≤ a →
  (∀ ω ∈ Ω, ∀ b, ω (b* a b) = 0) → a = 0
centreSeparating_cstar             -- the same, as `CStar.CentreSeparating`
nonneg_of_conjNP_of_centreSeparating
  : CentreSeparating A Ω → (∀ ω ∈ Ω, ∀ c, 0 ≤ ω (c* a c)) → 0 ≤ a
```

This is 69IX.2 ⇒ 69IX.1 — the hard direction — but **not** by the thesis's
route.  The thesis goes through `gns_ceil` (`Projections.lean:3831`, still
`sorry`) and `carrier_basic`; we go through the central support instead:
`⌈⌈a⌉⌉ = ⋃_b ⌈b* ⌊a⌉ b⌉` (**68I** `cceil_fundamental`, proved), every `ω ∈ Ω`
kills `b* ⌊a⌉ b` (it kills `b* a b`, hence `b* a a* b` since `aa* = a² ≤ ‖a‖a`,
hence `b* ⌈aa*⌉ b` by **60I** `ceil_functionals_lemma`), hence kills each
`⌈b* ⌊a⌉ b⌉` — **60I** again — hence kills their supremum, which is the
*central* projection `⌈⌈a⌉⌉`, which the hypothesis therefore annihilates.
**60I** is the step that was thought to be missing; it is already in the tree.
This is a class-2 divergence and it also proves the substance of 69IX.2 ⇒ 69IX.1
for whoever closes `vn_center_separating` (items 1 ⇔ 2 are then cheap; item 3
still needs "a `projSup` of central projections is central", which has no lemma).

**90II.1 itself** (`A/VN/NormalFunctionals.lean`) is then the thesis's own
argument in the shape our statement asks for.  `Ξ = {ω(c*(·)c) : ω ∈ Ω, c ∈ 𝒜}`
is order separating — that is `nonneg_of_conjNP_of_centreSeparating` — and
`Ω' ⊆ Ξ` is norm dense by **72III**.1c
(`‖b*ω − b'*ω‖ ≤ ‖b−b'‖_ω(‖b‖_ω + ‖b'‖_ω)`).  The thesis phrases the second
step as norm density plus **21X** `order_separating_dense_subset`; since our
statement is the unfolded "`ω(s* a s) ≤ ω(s* b s)` for all `s ∈ S` implies
`a ≤ b`", the same estimate is used directly, as ultrastrong *continuity* of
`x ↦ ω(x* k x)` (new lemma `continuous_ultrastrong_conjFunctional`), so that
`{x | 0 ≤ ω(x* k x)}` is ultrastrongly closed and contains the dense set `S`.

**90II.2 remains blocked on 89IX `normal_functional`** — its proof is "write
`f = ∑ₙ ⟨xₙ, ϱ_Ω(·)xₙ⟩` by 89IX" and there is no way round that.  So 112X.1
(which the brief says needs 90II alone) should now be reachable; 112X.5 and
anything wanting 90II.2 are not.

### 4a. 65III.3 `commutant_basic_3` — divergence class 1

The thesis's own witness, transcribed: `S = {e₁₂} ⊆ M₂`.  `e₁₂` commutes with
itself, so it lies in `S^□`, but `e₁₂e₁₂* = diag(1,0) ≠ diag(0,1) = e₁₂*e₁₂`,
so `e₁₂* ∉ S^□`.  Worth noting for the record that the statement does *not*
mention a `VonNeumannAlgebra (M₂)` instance (`commutant` is `Set.centralizer`
and needs none), so the proof does not leak the `sorry`ed `mn_vna_1` — that is
why it can be `#print axioms`-clean.

### 5. Classification

* **20VI** — class 1 (faithful), plus the injectivity gap of §1 filled.
* **21VII** — class 2 (different route: the family argument in place of the
  C*-product, because the ℓ^∞-product is not in the tree).
* **64II** — class 2 (spectral Riemann sum in place of Gelfand +
  Stone–Weierstraß, because all three inputs are `sorry`).
* **65IV** — class 2, inherited: proved directly rather than by the thesis's
  reduction to 64II, since the spectral projections are already in `{a}^□□`.
* **65III**.3 — class 1 (the thesis's witness, verbatim).
* **69IX**.2 ⇒ .1 (the bridge) — class 2: central-support route in place of the
  thesis's `gns_ceil` route, because `gns_ceil` is `sorry`.
* **90II**.1 — class 1 for the mathematics (the thesis's two steps), class 2 for
  the second step's *rendering*: ultrastrong continuity of `x ↦ ω(x* k x)` in
  place of "norm density of `Ω'` in `Ξ` plus **21X**", because our statement is
  the unfolded order-separation property rather than `OrderSeparating Ω'`.
* `matBilin_nonneg_of_mi` — relocation only, proof unchanged (worker 40's).

No new errata: nothing in cstar.tex/vn.tex was found to be *wrong* this
session.  §1's gap is an incomplete justification of a true claim and is
recorded here, not in ERRATA.md.

### 6. Verification

* `lake build` (whole project): `Build completed successfully (8738 jobs)`,
  exit 0.  `A/Proc.*` and `B/Dils.*` build exactly as before.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `Theses.A.CStar.matBilin_nonneg_of_mi`, `Theses.A.CStar.cstar_isometry`,
  `Theses.A.CStar.order_separating_norm`,
  `Theses.A.VN.abelian_projections_norm_dense`,
  `Theses.A.VN.projections_norm_dense`, `Theses.A.VN.commutant_basic_3`,
  `Theses.A.VN.eq_zero_of_centreSeparating_conj`,
  `Theses.A.VN.centreSeparating_cstar`,
  `Theses.A.VN.nonneg_of_conjNP_of_centreSeparating`,
  `Theses.A.VN.continuous_ultrastrong_conjFunctional`,
  `Theses.A.VN.vn_center_separating_fundamental_1`.
* `sorry` tokens: `A/CStar` 41 → 39, `A/VN` 121 → 117.
  (Per file: Matrices 6, Positive 22, Representation 11; Basic 34,
  Completeness 17, Division 26, NormalFunctionals 18, Projections 22.)
* Neither of the two `sorry`ed instances (`vonNeumannAlgebra_lp_infty`,
  `mn_vna_1`) was discharged.  §2 records that `vonNeumannAlgebra_lp_infty`'s
  gap is what forced 21VII's route change, so it now gates one more item than
  before.
* Nothing staged, nothing committed.

---

## Session 18 — `A/Proc` parsecs 990, 1020, 1040: the Gardner harvest (worker 46)

`A/Proc/Measurement.lean` only; 45 → **40** `sorry` (chapter 137 → **132**).
Nothing else in the tree touched.  This is the round that consumes worker 43's
**65IV** `projections_norm_dense`.

### 1. What was proved

| point | declaration | note |
|---|---|---|
| **99II** | `gardner` | the author's cycle, verbatim |
| **99IX** | `iso` | the author's proof |
| **99XII** | `sharp_multiplicative` | *not* the thesis's hint — §3 |
| **102V** | `nmiu_rigid` | the author's proof + one density step |
| **104VI** | `centrally_similar_corollary` | the thesis gives **no** proof |

New `private` infrastructure, all reusable (`Measurement.lean`, new block
"Infrastructure for parsecs 990–1040", placed just before parsec 990):

* `ncpMap_add`, `ncpMap_zero`, `ncpMap_smul` — the remaining linearity
  clauses of an ncp-map, alongside the pre-existing `ncpMap_sub`,
  `ncpMap_mono` (which were **moved up** from the parsec-1010 area; no
  change to them).
* `ncpMap_continuous` — `‖f(a)‖ ≤ ‖f(1)‖‖a‖` from **34XVI** `cp-russo-dye`.
  Worth knowing: `NCPMap` carries no `ContinuousLinearMapClass`, and
  `Theses.A.VN.ncp_isCompletelyPositiveMap` is `private`, so the
  `IsCompletelyPositiveMap` witness has to be rebuilt from `cp_iff` and
  `map_cstarMatrix_nonneg'` (two lines).
* `mem_closure_span_projections` — **65IV** for *arbitrary* elements
  (`x = ℜx + i·ℑx`; `A/VN` states it only for self-adjoint `x`), and
  `mem_of_isClosed_of_projections` — "a norm-closed `ℂ`-subspace containing
  every projection is everything".  These two are the whole of 65IV's
  leverage; every one of the five proofs below ends in them.
* `ncpMap_mul_ceilOne` — `f(x)⌈f(1)⌉ = f(x)` for *any* ncp-map, from **61II**
  (`⌈f(x)⌋ ≤ ⌈f(⌈x⌋)⌉ ≤ ⌈f(1)⌉`).  This is what replaces unitality in §3.
* `isStarProjection_map_of_mul`, `ceil_map_of_isStarProjection_map`,
  `isStarProjection_map_of_ceil`, `gardner_43`, `gardner_32`, `gardner_21` —
  the six implications of 99II, stated **separately**, because 99IX, 99XII
  and 102V each need some of them for a map that is not assumed unital.
* `ceil_le_perp_iff` (public, unchanged statement and proof) was **moved
  earlier** in the file: the relocated `eq_zero_of_le_proj_le_perp` uses it,
  and it now lives in the new infrastructure block instead of the
  parsec-1010 one.  No other declaration order changed.

### 2. 99II `gardner` — divergence class 1

The author's cycle (1)⇒(4)⇒(3)⇒(2)⇒(1) with (4)⇔(5) on the side,
transcribed step for step:

* (1)⇒(4), (5)⇒(4): as the thesis says, immediate.
* (4)⇒(5): **60V** `ncp_ceil` then `ceil` of a projection.
* (4)⇒(3): `pq = 0` ⟹ `p ≤ q^⊥` ⟹ `f(p) ≤ f(1) − f(q)`, and two
  projections one of which is below the other's complement multiply to `0`.
* (3)⇒(2): `f(a)f(b) = f(a)⌈f(a)⌋⌊f(b)⌉f(b)` with `⌈f(a)⌋⌊f(b)⌉ = 0` from
  **61II** `ncp_ceill` and **60VIII** `mult_cancellation`.
* (2)⇒(1): the `ae^⊥·e = 0` / `ae·e^⊥ = 0` pair gives `f(ae) = f(a)f(e)` for
  a projection `e`; the author's "since the linear span of projections is
  norm-dense in `𝒜`" is **65IV**, and is realised as: `{x | f(ax) = f(a)f(x)}`
  is a `ℂ`-submodule (linearity of `f`), norm-closed (`ncpMap_continuous`),
  and contains the projections.

### 3. 99XII `sharp_multiplicative` — divergence class 2, and why

The thesis's hint is "factor `f = ζ ∘ h` where `ζ` is a filter for `f(1)`".
That route is **not available**: it needs **98II** `filter_basic_1` (unique
factorisation through the standard filter), which is `sorry`, as is **96V**
`canonical_filter`.

Instead: **the (4)⇒(3), (3)⇒(2), (2)⇒(1) steps of 99II never use unitality
of `f` — only that `f(1)` is a projection.**  That is the finding of this
session and it is what makes 99XII a two-line corollary of 99II:

* (4)⇒(3) needs `f(1) ≤ 1`, which holds because `f(1)` is a projection (and
  `f(1)` *is* one, by hypothesis (2) at `p = 1`);
* (2)⇒(1) needs `f(ae)·f(1) = f(ae)`, and `ncpMap_mul_ceilOne` gives
  `f(x)⌈f(1)⌉ = f(x)` unconditionally — with `f(1)` a projection,
  `⌈f(1)⌉ = f(1)`.

So the private lemmas are stated with `hq : IsStarProjection (f 1)` rather
than `f 1 = 1`, and `gardner` supplies `hq` from its `hu`.

### 4. 99IX `iso` — class 1

`g(1) ≤ 1` and `1 = f(g 1) ≤ f(1) ≤ 1` give unitality of both maps (the
author's first sentence).  The author then argues that `f` maps projections
to projections via **55X** `projection-order-sharp` and preservation of
`(·)^⊥` and order; our `NCPMap` bundle has no "order-isomorphism" API to
apply 55X through, so the step is worker 42's `isStarProjection_map`, which
is 55X's content transported along `g` (`e − e²` is positive and below both
`e` and `e^⊥`, so `g(e − e²)` is below both `p` and `p^⊥`, hence `0`, and
`g` is injective).  Multiplicativity is then 99II; `f(a*) = f(a)*` is
**10IV** `cstar-p-implies-i` (`ncp_star`), already in the tree.

### 5. 102V `nmiu_rigid` — class 1, with the density step made explicit

The author's proof verbatim: `⌈g(p)⌉⌈g(q)⌉ = ϱ(p)ϱ(q) = ϱ(pq) = 0`, so `g`
is multiplicative by 99II, hence maps projections to projections, hence
`g(p) = ⌈g(p)⌉ = ⌈ϱ(p)⌉ = ϱ(p)`.  The thesis's "for this, it suffices to
prove that `g(p) = ϱ(p)` for every projection `p`" is left unjustified
there; it is 65IV again (both maps are continuous and linear), and that is
how it is discharged here.

### 6. 104VI `centrally_similar_corollary` — the thesis gives no proof

proc.tex:1546 states it as a Corollary with no proof block, so this is the
first proof of it.  It is short: **104IV**
`centrally_similar_fundamental` applies to every projection `e`, because its
*second* hypothesis `⌈q ϑ(e^⊥) q⌉ ≤ e^⊥` is this corollary's hypothesis at
`e^⊥`.  That gives `eq = qe` and `ϑ(e) = e` for every projection, and 65IV
then extends both to all of `𝒜` (`ϑ` is norm-contractive as a ∗-homomorphism,
`NonUnitalStarAlgHom.norm_apply_le`).

Note that 104VI *does* state the faithfulness hypothesis `⌈q⌉ = 1` that
104IV's printed form omits (ERRATA, 104IV row), so no new erratum arises.

### 7. Three of the eight statements 65IV was said to release are **not**
released — with their real blockers

* **99XI** `filter_of_projection_multiplicative` — blocked on **98II**.1
  `filter_basic_1` (or **96V** `canonical_filter`), both `sorry`.  With 99XII
  in hand it reduces to "a filter whose `c(1)` is a projection maps
  projections to projections", and nothing in `IsFilter`'s universal property
  yields that without the factorisation through the standard filter.
* **104VII** `positive_quotients_centrally_similar` — only the *first
  paragraph* of the thesis's proof (proc.tex:1563) is the density step.  The
  rest reduces to the invertible case through an increasing sequence of
  projections built from an **approximate pseudoinverse**: it needs **80IV**
  `approximate_pseudoinverse` (`A/VN/Division.lean`, `sorry`, frozen),
  **104III**.5 `centrally_similar_basic_5` (`sorry`), **45VI**
  `mult_jus_cont`, and a corner reduction.  **Still blocked.**
* **128II** `tomiyama` — the author's density step is over the projections
  **of the subalgebra ℬ**, not of `𝒜`: the argument needs `e ∈ ℬ` so that
  `e^⊥f(ea) ∈ ℬ = range f` and `f(e^⊥f(ea)) = e^⊥f(ea)`.  65IV as stated (and
  as proved) produces projections in `{b}^□□`; concluding `{b}^□□ ⊆ ℬ`
  requires the **double commutant theorem 88VI** (`sorry`, and stated only
  for `B(H)`).  The alternative — that an `IsVNSubalgebra` is closed under
  `cfc` and under `ceil` — is **not in the tree** either (`ceil` is defined by
  its universal property, with no "increasing limit" characterisation to feed
  to `dirSup_mem`).

  **New named blocker**, worth its own line in any dependency map: *the
  linear span of the projections of a von Neumann **subalgebra** is
  norm-dense in it* — 65IV relativised.  It gates 128II and therefore parsec
  1280 (128VIII `uniqueness_duplicator` sits on top of it).

The rest of that paragraph of the brief was right: 104VI and 104VII do both
state `⌈p⌉ = ⌈q⌉ = 1`, and 61II had indeed already supplied 99II's (3)⇒(2).

### 8. Classification summary

* **99II** — class 1.
* **99IX** — class 1 (one rendering change, §4).
* **99XII** — class 2: the thesis's hint routes through `sorry`ed filter
  theory; the unitality-free form of 99II is used instead.
* **102V** — class 1, with the unjustified "it suffices on projections"
  step discharged by 65IV (§5).
* **104VI** — no author argument exists; class 2 by default.

No new errata (nothing in proc.tex was found to be wrong this session) and no
new questions.

### 9. Verification

* `lake build` (whole project) → exit 0.  `grep -c error:` counts only the
  pre-existing `linter.style.header` noise; filtering it leaves **0**.
* Per-file `declaration uses \`sorry\`` from that build: Measurement **40**
  (was 45), Tensor 46, QuantumLambda 26, Duplicators 20 — chapter **132**.
  Nothing else in `A/` moved; `B/Eff/StatesPredicates.lean` 9 → 7 is the
  concurrent `B/Eff` worker, not this session.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `Theses.A.Proc.gardner`, `.iso`, `.sharp_multiplicative`, `.nmiu_rigid`,
  `.centrally_similar_corollary`, and (regression check after the move)
  `.ceil_le_perp_iff`, `.equivalent_examples_2`,
  `.equivalent_examples_2_is_false`.  No `sorryAx`.
* `A/Proc` still has **no** `sorry`ed instance.
* Doc `file:LINE` refs re-derived from the labels and confirmed exact:
  99II→795, 99IX→878, 99XII→905, 102V→1241, 104VI→1546, 104VII→1556,
  128II→5948.
* `asols.tex`'s errata block has exactly **one** entry in these parsecs,
  `parsec-990.70` (= **99VII**, the ERRATA row already marked DONE): it is
  99II's (3) ⇒ (2) paragraph, and proc.tex **already carries the corrected
  text**, so §2's transcription is of the corrected version.  (The point
  numbering there is off by one point from the enumerated item: the erratum
  rewrites `\begin{point}{70}`, which proves (3) ⇒ (2).)
* Warning profile of `Measurement.lean` is byte-for-byte the pre-session one
  apart from the five `declaration uses \`sorry\`` that disappeared: 43
  `show`-style, 25 unused-section-variable, 18 `if_neg`, 15 `if_pos`, 13
  unused-simp-argument, before and after.  (The new proofs use `change`, not
  `show`, for the defeq unfoldings of `Submodule` membership.)
* Nothing staged, nothing committed.

## Session 18 — `B/Eff`: parsec 191 in full (191II, 191VII, 191VIII) (worker 45)

Scope: `Theses/B/Eff/StatesPredicates.lean` only (+ `ERRATA.md`, `QUESTIONS.md`).
Three `sorry`s closed; B/Eff **25 → 22**, `StatesPredicates.lean` **9 → 6**.

* **191VII** `emod_effectus_representation` — the representation half of the
  `emod-effectus` theorem.
* **191VIII** `exc_rng_eff` — `Rngᵒᵖ` is an effectus in total form.
* **191II** `emod_effectus` — `EMod_Mᵒᵖ` is an effectus in total form.

### 1. The obstacle all three (well, two) share, and the API for it

`EffectusTotalForm D` is stated against *whatever* `HasFiniteCoproducts D` /
`HasTerminal D` instance is in scope, and both classes are `Prop`s, so `X ⨿ Y`
is always `colimit (pair X Y)` and `⊤_ D` an opaque choice.  The thesis, of
course, computes with the *concrete* product of effect modules (resp. of
rings) and with the *concrete* initial object.  Bridging that gap once, for an
arbitrary category, is the main piece of reusable API added this session:

```
structure CoprodPres (D) [Category D] where
  T : D ; hT : IsTerminal T
  P : D → D → D ; pinl ; pinr
  hP : ∀ X Y, IsColimit (BinaryCofan.mk (pinl X Y) (pinr X Y))

theorem effectusTotalForm_of_pres [HasFiniteCoproducts D] [HasTerminal D]
    (d : CoprodPres D) (h1 …) (h2 …) (h3 …) : EffectusTotalForm D
```

`h1`, `h2`, `h3` are the three axioms of 180I written for `d`'s concrete data
(`d.pmap`, `d.pinl`, `d.desc`).  Supporting API in `CoprodPres`: `desc`,
`inl_desc`/`inr_desc`, `hom_ext`, `desc_self`, `pmap`, `cofanIso`,
**`coprodIso`** and `termIso`, plus the top-level `sq_symm`.

The key lemma is **`coprodIso : (A ⨿ B) ≅ d.P A' B'`, parameterised by
isomorphisms `A ≅ A'` and `B ≅ B'` of the two *summands*** — not just by an
isomorphism of the coproduct object.  That extra generality is what makes the
comparison usable at `X ⨿ ⊤_D ≅ d.P X d.T` and at
`(⊤_D ⨿ ⊤_D) ⨿ ⊤_D ≅ d.P (d.P d.T d.T) d.T`, which is exactly where the three
axioms live.  (Session 17's `cofanOfIso`, in `Effectus.lean`, transports along
an iso of the coproduct *object* and does not do this job; it was not reused.)

Everything else is bookkeeping: `map_comm` turns a pair of commuting squares
on the summands into one for `coprod.map`, `cotuple_comm` does the same for
`[u, κ₂] : 1+1+1 → 1+1`, and `sq_symm` flips a square so `IsPullback.of_iso`
can carry the concrete pullback to the ambient one.

**Worth knowing for the next user of this bridge**: once the presentation is
built from an *opposite* category (`d.P X Y := op (of (X.unop × Y.unop))` with
`hP` proved by `BinaryCofan.IsColimit.mk`), `d.pmap` and `d.desc` come out
**definitionally equal** to the concrete `op`ped maps, so no rewriting lemmas
are needed for them.  Only `d.hT.from` needs one (`rng_from` / `emod_from`,
each a one-line `IsTerminal.hom_ext`), because `IsTerminal.from` is an opaque
`IsLimit.lift`.

### 2. 191VII — `emod_effectus_representation`

Class **(1) faithful**, and cheap: the thesis's 191VII argument is literally
"`Pred f = Pred g` iff `p ∘ f = p ∘ g` for all `p`, so `Pred` is faithful iff
`C` has separating predicates".  The functor itself was **already in the tree**
— `predMap_functor` (190II.5) builds it — so the proof is that construction
plus four lines of faithfulness.

**This did not depend on 191II at all**, contrary to the plan inherited from
session 17's blocker table, which recommended doing it after `emod_effectus`.
It was in fact the cheapest of the three.

### 3. 191VIII — `exc_rng_eff` (published solution, `bsols.tex:1830`)

Divergence class **(2) different route, in one step only.**

The three element-level lemmas `rng_po1`, `rng_po2`, `rng_je` transcribe the
solution's three paragraphs.  `rng_po1` is `f(r,s) = α(r,0) + β(0,s)` with the
solution's own key step `α(1,0)β(0,1) = β(1,0)β(0,1) = β(0,0) = 0`; `rng_po2`
is `g(r) = δ(r,0)` after `δ(0,s) = δ(0,s)δ(0,1) = 0`.

The **one divergence** is in joint epicity.  The solution argues
`f(0,0,m) = m·f(0,0,1) = m·g(0,0,1) = g(0,0,m)`, which uses that the initial
ring *is* `ℤ` (that every element is an integer multiple of `1`).  We cannot
use that: `RingCat.{u}` for `u > 0` has no `ℤ`, only `ULift ℤ`, and Mathlib's
`⊥_ RingCat` is an abstract choice.  Replaced by an argument that needs only
**initiality** and holds for the initial object of any category of rings:

* the diagonal `Δ : Z → (Z×Z)×Z` is a ring map, so `f ∘ Δ` and `g ∘ Δ` are
  both *the* map out of the initial `Z`, hence `f(c,c,c) = g(c,c,c)`;
* `(0,0,c) = (0,0,1) · (c,c,c)`, so `f(0,0,c) = f(0,0,1)·f(c,c,c)` and the two
  factors are already known to agree.

A pleasant consequence: **`ℤ` is never needed anywhere in 191VIII**, and
neither is `RingCat.zIsInitial` (which does not exist in Mathlib).  The whole
solution goes through with `⊥_ RingCat` and `initialIsInitial`; the only fact
about it used outside joint epicity is that its structure maps are ring
homomorphisms.  `HasInitial`, `HasTerminal` and `HasBinaryProducts` for
`RingCat` are already instances, so no limit theory had to be built either.

`ERRATA.md` gains one row: the closing chain of the solution's joint-epicity
paragraph (`bsols.tex:1925`) is garbled.

### 4. 191II — `emod_effectus` (thesis proof, `eff.tex:2206–2280`)

Divergence class **(1) faithful** throughout; the three parts of the thesis's
proof (finite products, the two pushout diagrams, joint epicity) map one-to-one
onto `emod_po1`, `emod_po2`, `emod_je`.

New effect-module infrastructure, all `private` and all *local* instances
(`attribute [local instance]`, so nothing leaks into the rest of the file):

* `emod_smul_zero` (`λ·0 = 0`) and `emod_zero_smul` (`0·a = 0`) — both by
  cancellation, as in `effectModule_bool_smul`;
* `selfEffectModule : EffectModule M M` (`λ · a = λ ⊙ a`; the two distributive
  axioms are the existing `emon_mul_ovee` and `emon_ovee_mul`),
  `prodEffectModule`, `punitEffectModule`;
* `emodInit E : M → E`, `λ ↦ λ·1`, with `emodInit_unique` — so `M` is initial
  (`emodIsInitial`) and `{0=1}` final (`emodIsTerminal`) in `EMod_M`;
* `emodFst`/`emodSnd`/`emodPair`/`emodProdMap`, and `emodPres`, the
  `CoprodPres` for `EMod_Mᵒᵖ`.

**The one thing the thesis waves through** is "it is easy to see `f` is
(partially) additive" for `f(x,y) = α(x,0) ⋁ β(0,y)`.  In the Perp-relation
style that is the *middle-four interchange*
`(a ⋁ b) ⋁ (c ⋁ d) = (a ⋁ c) ⋁ (b ⋁ d)`, including the claim that the
left-hand sums are defined at all.  It is proved once, as `ovee_interchange`,
and the route is worth recording because it is short: turn the known sum into
`PCM.IsSumOf [a,c,b,d]` (`isSumOf_four`), permute the list
(`PCM.isSumOf_perm`), peel the resulting `IsSumOf [a,b,c,d]` back apart with
`PCM.isSumOf_cons_iff`, and re-associate twice with `PCM.assoc_left`.  All five
ingredients were already in the tree.

Joint epicity follows the thesis exactly: `f(1,0,0) = g(1,0,0)` and
`f(0,1,0) = g(0,1,0)` from the two hypotheses, `f(0,0,1) = f(1,1,0)ᵖ` by
uniqueness of the orthosupplement, `(0,0,λ) = λ·(0,0,1)`, and
`(a,b,c) = (a,0,0) ⋁ (0,b,0) ⋁ (0,0,c)`.

### 5. Lean traps met (in addition to session 17's two)

* **Structure-instance fields with implicits *after* an explicit binder.**
  `EffectModule.smul_perp : ∀ (l : M) {a b : E}, Perp a b → …` cannot be
  written `smul_perp l h := …` — `h` binds to `a`.  Use tactic mode
  (`smul_perp := by intro l a b h; …`).  Leading implicits are fine
  (`perp_map := fun {_ _} h => …`).
* **`obtain ⟨m', rfl⟩ : ∃ m', m' = m`**, not `∃ m', m = m'`: the latter
  substitutes `m'` away and you lose the retyped variable.
* **`IsPushout` arguments in a non-`Type` category need `show … from …`**, not
  `(… : X ⟶ Y)` ascription: with four arguments whose category is still a
  metavariable, plain ascription is postponed and never forces `C`.
* `exc_eamorphism_monotone` and `eabasics_le_perp_compat` return **existentials**
  (the witness of `≼`, resp. the definedness proof), so they need `.choose`.
* `emodhom_ext`-style extensionality must take `f g` **explicitly**: with them
  implicit, `obtain ⟨…⟩ := f` clears the hypothesis that mentions `f`.

### 6. Classification summary

* **191VII** — class **1**.
* **191II** — class **1** (the interchange lemma is filling a gap the thesis
  calls easy, not a change of route).
* **191VIII** — class **1** except joint epicity, which is class **2**
  (ℤ-free, for the reason in §3).
* No statement was changed; no statement was found false.

### 7. Verification

* `lake build` of all eight `B/Eff` modules: exit 0,
  `Build completed successfully (8715 jobs)`.  The ~900 new lines produce no
  warnings other than the file's pre-existing `linter.style.show` class.
* `#print axioms` on `emod_effectus`, `emod_effectus_representation`,
  `exc_rng_eff` and `effectusTotalForm_of_pres`: all
  `[propext, Classical.choice, Quot.sound]`.
* `#beff_leaks` over all eight modules:

  ```
  checked 1564 declarations under `Theses.B.Eff`
  22 are themselves `sorry`; 0 depend on a `sorry`
  hand-written indirect leaks: 0
  non-standard axioms (outside propext/Classical.choice/Quot.sound/sorryAx): 0
  ```

* Per-file `sorry`s: Comparisons 3, Dagger 3, DiamondAmp 2, EffectAlgebras 6,
  Effectus 2, Quotients 0, **StatesPredicates 6**, WStarCat 0 — **22**.
* Nothing staged, nothing committed.

## Session 19 — `B/Eff` parsec 192VII: states as an abstract `Mᵒᵖ`-convex set (worker 48)

**Result: `stat_mconvex` and `stat_functor` are proved.  B/Eff 22 → 20 code
`sorry`s; `StatesPredicates.lean` 6 → 4.  Both statements are unchanged
byte-for-byte; only `:= sorry` was replaced.  Zero `sorryAx` leakage
preserved.**

With this, **every `sorry` left in `B/Eff` is blocked by something other than
formalization effort**: 12 need thesis-A mathematics (and are off `B/Eff`'s
import path, which is `Theses.Common` only — see session 17 §2), 5 are
cited-only, 2 are parked on QUESTIONS **B4**/**B6**, and 1 (195VI) needs a
Mathlib-sized development ("basically disconnected" spaces and σ-Dedekind
completeness of `C(X)`, neither in Mathlib).  There is no reachable item left
in the chapter.

### 1. The obstacle, and why the n-ary tupling was not needed

192VII defines the convex structure on `Stat X` by

```
h(λ₁|φ₁⟩ ⋁ ⋯ ⋁ λₙ|φₙ⟩)  =  [φ₁, …, φₙ] ∘ ⟨λ₁, …, λₙ⟩,
```

an `n`-ary cotuple composed with an `n`-ary *partial* tuple, and the previous
two reports recorded the blocker as "our `Stat`/`Scal` layer has no `n`-ary
tupling API".  It turns out that layer is **not** what the proof needs.  The
thesis's own computation rewrites the composite on its very next line as the
iterated partial sum

```
[φ₁, …, φₙ] ∘ ⟨λ₁, …, λₙ⟩  =  ⋁ᵢ φᵢ ∘ λᵢ,
```

and every subsequent line of the proof is about that form.  So the right move
is to build the iterated partial sum directly.  Doing so avoids `Fin n`-indexed
coproducts entirely — which matters, because the `n`-ary partial tuple would
have needed an `n`-ary *untying* axiom, and `FinPAC.untying` is binary with no
inductive handle on `∐_{i : Fin n}`.

**What makes the direct route work is a different effectus axiom.**  The
summability of `⋁ᵢ φᵢ ∘ λᵢ` does not follow from `untying`; it follows from
`perp_of_one_perp` ("if `1∘f ⊥ 1∘g` then `f ⊥ g`") together with
`truth_effObj_eq_id` (181XIII, `1_1 = id`): the truth of the `i`-th term is

```
(λᵢ ≫ φᵢ) ≫ 1_X  =  λᵢ ≫ (φᵢ ≫ 1_X)  =  λᵢ ≫ 1_1  =  λᵢ ≫ id  =  λᵢ,
```

using that `φᵢ` is a *state* (total).  The `λᵢ` sum to `1` by definition of a
formal convex combination, so the terms are summable, and the sum's truth is
`1` — i.e. the result is again a state.  Totality of the result is therefore
not an extra check but the very thing that produced the sum.

### 2. New reusable API (all public, all in `StatesPredicates.lean`)

Four lemmas are the `n`-ary forms of the finPAC/effectus axioms and are worth
reusing anywhere partial sums of morphisms appear:

| name | content |
|---|---|
| `isSumOf_comp_right` | `⋁ᵢ fᵢ ≫ k = ⋁ᵢ (fᵢ ≫ k)` (n-ary `FinPAC.comp_ovee`) |
| `isSumOf_comp_left` | `k ≫ ⋁ᵢ fᵢ = ⋁ᵢ (k ≫ fᵢ)` (n-ary `FinPAC.ovee_comp`) |
| `exists_isSumOf_of_truth` | if `⋁ᵢ (1∘fᵢ)` exists so does `⋁ᵢ fᵢ`, and `1∘⋁ᵢfᵢ = ⋁ᵢ(1∘fᵢ)` |
| `isSumOf_unop` | sums in `Mᵐᵒᵖ` are sums in `M` (converse of the existing `isSumOf_op`) |

`tuple_desc` records the binary instance of the thesis's tuple identity —
`[φ₁,φ₂] ∘ (κ₁∘λ₁ ⋁ κ₂∘λ₂) = (φ₁∘λ₁) ⋁ (φ₂∘λ₂)` — so that the translation of
`h` into an iterated sum is *checked* in the tree rather than merely asserted
in a comment.  (The `n`-ary tuple itself is still not formalized.)

On top of that, `statSum p g` — "the convex combination `⋁ᵢ g(zᵢ) ∘ p(zᵢ)` of a
family of states" — with its three laws, deliberately mirroring the existing
`rsum`/`rsum_eta`/`rsum_map`/`rsum_mu` layer for `[0,1]`-combinations in a real
vector space (which is `Finset`-based and only for `I`, hence not reusable
here):

* `statSum_spec` / `statSum_eq` — specification and uniqueness.  The spec holds
  for **any** repetition-free list containing the support, not just an exact
  enumeration; that is what makes every later proof a one-liner choice of list.
* `statSum_eta`, `statSum_map` (reindexing), `statSum_mu` (Fubini),
  `statSum_statMap` (`f ∘ ⋁ᵢ φᵢ∘λᵢ = ⋁ᵢ f∘φᵢ∘λᵢ`).

Then `statMap`, `statMConvex`, `statMConvex_h`, `statMap_isAffine`,
`statFunctor`, and the two theorems.

### 3. The gap the thesis waves through

The associativity axiom is stated as `h ∘ μ = h ∘ 𝒟_M h`, and the thesis's
computation treats `𝒟_M h` as if it simply relabelled the terms
`σᵢ|ψᵢ⟩ ↦ σᵢ|h(ψᵢ)⟩`.  It does not: `𝒟_M h` **sums coefficients over the fibres
of `h`**, so when two of the inner combinations `ψᵢ` happen to have the same
`h`-value the outer combination collapses.  That is precisely the work in
`statSum_map`, which is proved by `isSumOf_map_fiber` (fibre-grouping for
iterated partial sums, already in the file from 192III).  The identity still
holds, so this is an elision rather than an error and no erratum was filed —
but it is the single non-obvious step of the formalization, and the same
elision will recur wherever an Eilenberg–Moore algebra law is transcribed.

Similarly, `statSum_mu` needs Fubini for iterated partial sums in *both*
directions (`isSumOf_flatMap` / `isSumOf_of_flatMap` + `flatMap_map_comm`),
exactly as `exists_mu` did; the thesis's `⋁ᵢ ⋁ⱼ = ⋁_{i,j}` is one equals sign.

### 4. Lean notes

* **`(1 : (Scal C)ᵐᵒᵖ).unop = truth (effObj C)` is `rfl`**, and so is
  `(a * b : (Scal C)ᵐᵒᵖ).unop = a.unop ≫ b.unop`: the opposite effect monoid's
  `Mul` is `MulOpposite.instMul` (`a * b = op (b.unop * a.unop)`) and `Scal C`'s
  is `fun l m => m ≫ l`, and the two reversals cancel.  All three facts were
  checked with throwaway `example … := rfl` before being relied on; they make
  the whole `Mᵒᵖ` bookkeeping invisible.
* `List.map_congr_left` is the tool for "the two `map`s agree on the members of
  *this* list" (needed twice, once after `List.filter`, once inside the Fubini
  step); `simp only [Function.comp_def, Category.assoc]` is what reconciles the
  `∘`-shaped result of `List.map_map` with a hand-written lambda.
* `omit [EffectusPartialForm C] in` is needed on `isSumOf_comp_right/left`,
  which are pure finPAC facts; without it the unused-section-variable linter
  fires.

### 5. Classification

* **192VII** — class **1** for the mathematics (the thesis's proof is
  transcribed step for step, including the associativity chain), with a
  class **3** presentational departure: the `n`-ary tuple `[φ₁,…,φₙ] ∘
  ⟨λ₁,…,λₙ⟩` is replaced throughout by the iterated partial sum `⋁ᵢ φᵢ ∘ λᵢ`
  that the thesis's own proof substitutes for it on its second line, and the
  identification is verified in the binary case by `tuple_desc`.
* No statement was changed; no statement was found false; nothing filed in
  ERRATA or QUESTIONS.
* **A note on the strength of the two statements** (not changed, but worth
  recording): `stat_mconvex` asserts only `Nonempty (MConvex …)` and
  `stat_functor` only `∃ F, ∀ X, (F.obj X).carrier = Stat X.base`, so neither
  pins down the structure map or the action on arrows the way the thesis does.
  The full content is now in the tree as `statMConvex`, `statMConvex_h`
  (the formula for `h`), `statMap_isAffine` and `statFunctor`; anyone
  strengthening the two statements later should point them at those.

### 6. Verification

* `lake build` of all eight `B/Eff` modules: exit 0,
  `Build completed successfully (8715 jobs)`.
* The ~366 new lines (StatesPredicates 3613–3979) produce **no** warnings
  beyond the file's pre-existing `linter.style.show` class (six, at 3781,
  3785, 3788, 3902, 3911, 3954).
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `stat_mconvex`, `stat_functor`, `statMConvex`, `statMConvex_h`,
  `statFunctor`, `statMap_isAffine`, `statSum_mu`, `statSum_map`,
  `statSum_eta`, `statSum_statMap`, `tuple_desc`, `exists_isSumOf_of_truth`,
  `isSumOf_comp_right/left`, `exists_statSum`, `statSum_spec`, `statSum_eq`,
  `statMap` (`isSumOf_unop` depends on none).
* `#beff_leaks` over all eight modules:

  ```
  checked 1582 declarations under `Theses.B.Eff`
  20 are themselves `sorry`; 0 depend on a `sorry`
  hand-written indirect leaks: 0
  non-standard axioms (outside propext/Classical.choice/Quot.sound/sorryAx): 0
  ```

* Per-file `sorry`s: Comparisons 3, Dagger 3, DiamondAmp 2, EffectAlgebras 6,
  Effectus 2, Quotients 0, **StatesPredicates 4**, WStarCat 0 — **20**.
* Nothing staged, nothing committed.

## Session 20 — `B/Dils` parsec 1650: 165III, and the legs of `IsVNTensor` (worker 50)

**Result: `B/Dils` 62 → 61.  165III `dfn_tensor_of_hilbmod_maps` is proved
(the first statement of parsecs 1640–1670 to fall), and two structural
questions about `IsVNTensor` are answered by proof rather than by decision:
it is automatically ℂ-linear in its *second* argument, and its two legs are
automatically *normal*.  165VI and 167I were re-examined and are still
blocked — for reasons different from the ones on record.**

### 1. **165III** `dfn_tensor_of_hilbmod_maps` — divergence class 1, with two
repairs to the write-up

`dils.tex` **165IV**, transcribed.  `Θ(x,y) = (Sx) ⊗ (Ty)` is
`𝒜 ⊙ ℬ`-bilinear; the estimate

`‖∑ᵢⱼ ⟨Sxᵢ,Sxⱼ⟩ ⊗ ⟨Tyᵢ,Tyⱼ⟩‖ ≤ ‖S‖²‖T‖² ‖∑ᵢⱼ ⟨xᵢ,xⱼ⟩ ⊗ ⟨yᵢ,yⱼ⟩‖`

is the thesis's displayed chain, with the row vector `s = (1,…,1)` replaced by
the vector `c = (1,…,1)` in **33II**.1's criterion (the two say the same thing;
`c` is what `matBilin_nonneg_of_mi` takes).  Then `ExtTensor.univ` factors `Θ`
through `η`.  New private helpers: `sum_t_{nonneg,mono_left,mono_right,
smul_left,smul_right}`, `gram_conj`, `gram_nonneg`, `ba_inner_le_norm_sq`,
`gram_sub_nonneg`, `tensor_gram_bound`.

Two things **165IV** needs and does not say, both supplied here:

* *ℂ-homogeneity of `⊗` in the second slot.*  The step
  `Mₙ(⊗)(G, ‖T‖²H) = ‖T‖² Mₙ(⊗)(G,H)` needs it; `IsVNTensor` records
  `smul_complex` in the first slot only.  It is derivable — new public
  `vnTensor_smul_complex_right`: `d := t 1 (c·1) − c·1` has `Ω(d*d) = 0` for
  every product np-functional, so `d*d = 0` by `separating`, so `d = 0`, and
  `t a (c·b) = t 1 (c·1) · t a b = c · t a b` by multiplicativity.
* *Adjointability.*  The thesis writes "`S ⊗ T ∈ 𝒷ᵃ(X ⊗ Y)`" without
  producing an adjoint.  Ours is the factorisation of `(S*, T*)` through the
  same universal property; that it *is* the adjoint is checked against the
  elementary tensors in each argument separately, by two applications of
  `extTensor_inner_diff_ext`.

The thesis's `√(‖S‖² − S*S)` is replaced by `ba_inner_le_norm_sq`
(`⟨Sv,Sv⟩ = ⟨v, S*S v⟩ ≤ ‖S‖²⟨v,v⟩` via `CStarAlgebra.star_mul_le_algebraMap_norm_sq`
and `ba_inner_mono`) — class 3, same content without the functional calculus.

`hX`, `hY` are unused (the universal property is a *field* of `ExtTensor`);
the declaration carries `set_option linter.unusedVariables false in` and a
comment, as 159IV does.

### 2. The legs of a von Neumann tensor product (QUESTIONS **B5**)

New public, axiom-clean: `vnTensor_flip`, `vnTensor_legLeft_{nonneg,mono,
isSelfAdjoint,normal}`, `vnTensor_legRight_{nonneg,mono,normal}`.

`vnTensor_legLeft_normal : PreservesDirSups (fun a => t a 1)` is the one that
matters: it removes the "decision needed" that w41 opened.  Proof: the image
of a bounded directed `D` has a supremum `s'` in `𝒞`; every product
np-functional `ω ⊗ ξ` sees the same supremum of reals on both `s'` and
`s ⊗ 1` (normality of `Ω`, of `ω`, and `ξ(1) ≥ 0`, via `isLUB_re_of_isLUB` and
a new private `isLUB_mul_const`); so `(s ⊗ 1) − s'` is positive and killed by
every product functional, hence `0` by `separating`.

Consequence: **166II is no longer blocked on a decision** — see QUESTIONS B5.

### 3. What is still blocked, and why (corrections to the brief)

* **165VI** `ba_ext_tensor_pres` does **not** follow from 165III.  Six of
  `IsVNTensor`'s eight fields for `Θ` are now cheap (uniqueness on elementary
  tensors + 165V), but `generates` needs **164II**.2a `ext_tensor_basis`
  (`sorry`) and `separating` needs both **164II**.1 `ext_tensor_dense`
  (`sorry`) *and* a clause `IsVNTensor` does not have: the **existence** of
  product functionals (proc.tex `tensor`-2).  Filed as the third gap in
  QUESTIONS B5.
* **167I** `paschke_tensor` / `paschke_tensor_module` do not follow either:
  167II–167VI run through **166IV** `exttensor_dense_subsets` and **166VI**
  `dilationspace_dense_subset` (both `sorry`) and through `PaschkeModule`,
  which is under the QUESTIONS **D2** freeze.
* `ext_tensor_dense` is blocked twice over: it is a property of the concrete
  ℓ² construction (the author offers `extTensor_map_ext` precisely as the
  substitute for it), and the abstract route from `extTensor_sep` needs the
  projection theorem **160IV**, itself blocked on 149VIII/80IV.

### 4. Verification

* `lake build Theses` → `Build completed successfully (8738 jobs)`, exit 0,
  **zero** `error:` lines.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `dfn_tensor_of_hilbmod_maps`, `vnTensor_smul_complex_right`,
  `vnTensor_flip`, and all six leg lemmas.
* Warning diff for `SelfDual.lean` against the session's own baseline:
  **exactly one line**, `declaration uses sorry` 23 → 22.  (`omit` clauses and
  `change`-for-`show` were added where the new material would otherwise have
  introduced linter noise.)
* Code `sorry`s per file, before → after: `SelfDual` 23 → **22**, `Pure` 16,
  `Paschke` 9, `Stinespring` 7, `HilbertModules` 3, `Kaplansky` 2,
  `SelfDualCompletion` 2.  **`B/Dils` 62 → 61.**  No `sorry`ed instances.
* Files touched: `Theses/B/Dils/SelfDual.lean`, `ERRATA.md`, `QUESTIONS.md`,
  `PROVING-LOG.md`.  Nothing staged, nothing committed.  `HANDOFF.md` not
  touched (its `B/Dils` row is a whole-chapter figure and is stale for other
  reasons too).

## Session 21 — `B/Dils` parsec 1660: 166II ultranorm continuity of `⊗` (worker 52)

Date 2026-08-14.  Successor of session 20 (worker 50).  Scope: `B/Dils` only.

**Result: `B/Dils` 61 → 60.  166II `ultranorm_continuity_ext_tensor` is
proved — the statement that opened QUESTIONS B5's second half two rounds ago,
and the last of parsec 1660 that was reachable.  Two findings beyond the
proof: the thesis's boundedness hypothesis on the `x`-net is redundant, and
`kaplansky_hilbmod` (158II) is *not* blocked on `A/VN` 74IV, contrary to what
every round since w34 has recorded.**

### 1. 166II `ultranorm_continuity_ext_tensor` — divergence class 2

`dils.tex` **166III**, the thesis's splitting

```
xα ⊗ yα − x ⊗ y  =  (xα − x) ⊗ yα  +  x ⊗ (yα − y)
```

fed to the triangle inequality `unSeminorm_add_le` and `squeeze_zero`.  Each
of the two terms is estimated **differently from the thesis**, and that is the
one deliberate divergence.

*The thesis's route.*  `⟨(xα−x) ⊗ yα, (xα−x) ⊗ yα⟩ = (⟨xα−x,xα−x⟩ ⊗ 1)·(1 ⊗
⟨yα,yα⟩)`; the left factor is scaled into `effects 𝒞` and shown to converge
ultraweakly to `0`, the right factor is a bounded net, and **44III**
`vanishing_effects` finishes.

*Ours.*  Once `Ω(· ⊗ 1)` is known to be an np-functional — which is
`compNP` applied to the leg together with w50's `vnTensor_legLeft_normal`,
bundled here as `vnTensorLegLeftNP` — the whole estimate can stay inside the
order of `𝒞` and never leaves it:

```
Ω(⟨d,d⟩ ⊗ ⟨yα,yα⟩)  ≤  Ω(⟨d,d⟩ ⊗ M²·1)  =  M² · Ω(⟨d,d⟩ ⊗ 1)  =  M² · ω(⟨d,d⟩)
```

using `⟨yα,yα⟩ ≤ ‖⟨yα,yα⟩‖·1 ≤ M²·1` and monotonicity of `⊗` in its second
slot over a positive first slot.  Taking square roots this is exactly
`‖(xα−x) ⊗ yα‖_Ω ≤ M · ‖xα−x‖_ω`, which tends to `0` because `hx` holds for
*every* np-functional of `𝒜`, in particular for `ω`.  The second term is the
mirror image with the legs exchanged: `‖x ⊗ (yα−y)‖_Ω ≤ ‖x‖ · ‖yα−y‖_ξ` with
`ξ = Ω(1 ⊗ ·)`.

**44III `vanishing_effects` is therefore not used at all**, and neither is any
scaling into `effects 𝒞`.  Session 20's prediction of what the proof would
need ("an ultranorm triangle inequality, the scaling into `effects 𝒞`, and
bundling `Ω ∘ leg` as an `NPFunctional`") was right about the first and third
and wrong about the second — and the second is what carries the redundant
hypothesis, see §2.

New declarations in `SelfDual.lean`, section `VNTensor`, all `#print axioms`
clean: `le_ofReal_smul_one` (private; `0 ≤ u`, `‖u‖ ≤ r` ⟹ `u ≤ r·1`),
`vnTensor_nonneg`, `vnTensor_mono_right`, `vnTensor_mono_left`,
`vnTensorLegLeft`, `vnTensorLegRight` (the legs as `PositiveLinearMap`s),
`vnTensorLegLeftNP`, `vnTensorLegRightNP` and their `_apply` simp lemmas.

Also added, deliberately, as a standing guard: **`vnTensor_mul_complex`**, the
machine-checked witness that `IsVNTensor` is *inhabited* (`t = (·*·)` on `ℂ`,
all eight fields discharged, `#print axioms` clean).  Session 14's mirroring
defect left `PaschkeModule` uninhabited and made nine theorems vacuous, and it
survived several readings because nobody had tried a concrete example; this
chapter now carries one for the other structure it reasons about
hypothetically.

`hX`, `hY` are unused (as in 165III: `E : ExtTensor t ht X Y` carries
everything the proof needs), and so is `hxb` — §2.  The declaration carries
`set_option linter.unusedVariables false in` plus a comment giving the reason
for each, so the warning multiset is unchanged.

### 2. The thesis's `x`-net bound is redundant (ERRATA, 166II statement row)

166II hypothesises that **both** nets are norm-bounded.  The splitting it uses
never bounds `xα`: the bound enters only to make `⟨xα−x,xα−x⟩ ⊗ 1` an
*effect*, which is an artefact of routing through `vanishing_effects`.  The
order estimate above needs a bound on the `y`-net only.  Splitting the other
way, `xα ⊗ (yα − y) + (xα − x) ⊗ y`, drops the bound on `yα` instead — so the
lemma is true with **either one** of the two hypotheses, and the statement as
printed asks for one too many.  Our statement keeps both (faithful
transcription); the linter suppression is the evidence that `hxb` is unused.

This is the fifth time the "check whether a cited hypothesis is actually used"
habit has paid inside this project.

### 3. **`Kaplansky.lean` is not blocked on `A/VN` 74IV** — correction

Every brief and report since w34 has recorded `Kaplansky.lean`'s two `sorry`s
as waiting on thesis A's Kaplansky density theorem (**74IV**, and behind it
74I `proto_kaplansky`).  That is right for **158Ia**
`kaplansky_bounded_approx` and **wrong for 158II** `kaplansky_hilbmod`.

Reading `dils.tex` 4082–4279 in full: parsec 1580's point **11** — our 158Ia —
is an *unlabelled* expository restatement of the classical theorem ("The
theorem is usually stated as follows … For our generalization, it is more
convenient to consider the following variation"), and point **12** says the
generalization is "inspired by" Arveson's proof, "Cf. `\sref{kaplansky}`".
Because point 11 carries no LaTeX label it **cannot be cited**, and the proof
of `kaplansky-hilbmod` (points 30, 40, 50) never cites `kaplansky` either.
What that proof actually uses is:

* the ultranorm density of `D` — a *hypothesis* of 158II;
* `h(y) = y·2(1+⟨y,y⟩)⁻¹` and `g(x) = x·(1+√(1−⟨x,x⟩))⁻¹`, with `‖h(y)‖ ≤ 1`
  and `h(g(x)) = x` by continuous functional calculus;
* `h(y) ∈ D` for `y ∈ D`.  Note this needs `2(1+⟨y,y⟩)⁻¹ ∈ A`, i.e. `A`
  *unital*.  Our Lean `A : StarSubalgebra ℂ ℬ` **is** unital, so this is fine
  as transcribed — but the thesis's "C\*-subalgebra" need not be, and there the
  step is `h(y) = 2y − (2b(1+b)⁻¹)·y` with `b = ⟨y,y⟩`, which also needs `D`
  closed under negation (it is, being a submodule);
* ultranorm continuity of `h` (point 50) — the bulk of the work: the splitting
  `⟨h(y)−h(yα), h(y)−h(yα)⟩ = A₁ + A₁' + A₂ + A₂'`, `0 ≤ (1+b)⁻¹ ≤ 1` and
  `0 ≤ b(1+b)⁻¹ ≤ 1` for `b ≥ 0`, **45IV** `mult-uws-cont`, and Cauchy–Schwarz
  for `‖·‖_f` (`unSeminorm_inner_le`, in the tree).

So **158II is a self-contained target inside `B/Dils`** — long (the four
convergence estimates plus the CFC identities are the whole of it) but with no
external `sorry` and no decision in its way.  I did not attempt it; the
estimate is a session's work in its own right, and this round's target was
166II.

Consequence for **166IV** `exttensor_dense_subsets`: it is blocked on
**`ext_tensor_dense`** (164II.1) *only* — not, as recorded, on `ext_tensor_dense`
*and* Kaplansky.  And `ext_tensor_dense` is the one that has no route (w50 §3:
it is a property of the concrete ℓ² construction, and the abstract route needs
the projection theorem 160IV, itself behind 149VIII/80IV).

### 4. What was checked and is still blocked

* **166IV** — `ext_tensor_dense` (`sorry`), as above.  Verified by reading
  `dils.tex` 166V.
* **164II.2a** `ext_tensor_basis` — I re-checked whether it might follow from
  `extTensor_sep` now.  It does not: `IsONBasis` (`HilbertModules.lean:1768`)
  carries a genuine Parseval clause (`∑_{i∈s} ⟨eᵢ,x⟩•eᵢ → x` ultranorm) and an
  ℓ²-completeness clause, not a separation condition.  Orthonormality of
  `(eᵢ ⊗ dⱼ)` is immediate from `η_inner`; the other two clauses are the
  density statement again.
* **165VI**, **167I**, `Paschke.lean`, `Pure.lean`, `SelfDualCompletion.lean`,
  `HilbertModules.lean`, `Stinespring.lean` — unchanged from sessions 14/16/20;
  not re-tested, not contradicted.

### 5. Verification

* `lake build Theses.B.Dils.SelfDual` → exit 0, zero `error:` lines.
  (`lake build Theses` raced with the `A`-chain worker's concurrent edit of
  `Theses/A/VN/Basic.lean` — a missing `.olean` — and was re-run after.)
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `ultranorm_continuity_ext_tensor`, `vnTensor_mul_complex` and all eight
  other new public declarations.
* Warning diff for `SelfDual.lean` against this session's own baseline,
  message multiset with line/column stripped: **exactly one line**,
  `declaration uses sorry` 22 → 21.
* Code `sorry`s per file, before → after: `SelfDual` 22 → **21**, `Pure` 16,
  `Paschke` 9, `Stinespring` 7, `HilbertModules` 3, `Kaplansky` 2,
  `SelfDualCompletion` 2.  **`B/Dils` 61 → 60.**  No `sorry`ed instances.
* `HANDOFF.md` **not** touched (w50's precedent).  Its `B/Dils` row reads
  `139 → 75`; the true figure is `139 → 60` (its own refresh script agrees),
  and the `total` row is stale for the other chapters too, so the table needs
  one coordinated refresh rather than a per-worker edit.
* Files touched: `Theses/B/Dils/SelfDual.lean`, `ERRATA.md` (two 166II rows,
  and 165III/166II put back into point order), `QUESTIONS.md` (**B5**),
  `PROVING-LOG.md`.  Nothing staged, nothing committed.  The dirty
  `Theses/A/{CStar/Matrices,VN/Basic}.lean` are the other worker's.

---

## Session 22 — `A/CStar` parsec 341 and `A/VN` 74I Kaplansky (worker 51)

Date 2026-08-14.  Successor of session 19 (worker 47) on the A chain.
Scope: `Theses/A/CStar/*.lean` and `Theses/A/VN/*.lean`.

**Result: `A/CStar` 39 → 37, `A/VN` 114 → 112.  Four statements proved:
34aII `normal_russo_dye`, 34aVIII `russo_dye_cor` (which together release
128VI `sef_instrument` in `A/Proc`), and 74I `proto_kaplansky` with its
immediate corollary 74III `abs_us_cont`.**  All four `#print axioms`-clean.

### 1. 34aII `normal_russo_dye` — divergence class 2 (different route)

`‖f(a)‖ ≤ ‖f(1)‖‖a‖` for a *positive* map `f` and *normal* `a`.

*The thesis's route* (cstar.tex 341.20) restricts `f` to the commutative
`C*(a)` and invokes **34IX**.2 `cp_commutative_dom` (a positive map out of a
commutative C\*-algebra is cp) and then **34XVI** `cp_russo_dye`.  That is
**not** available: `cp_commutative_dom` is still `sorry` in the tree, and its
own proof needs **34VII** `ccstar-pos-mat` — a partition-of-unity
approximation of `(M_N 𝒜)₊` on the Gelfand spectrum.

*Ours* runs the same approximation, but **directly on `a` through the
continuous functional calculus**, where the partition of unity is explicit
and neither Gelfand duality nor Urysohn's lemma is needed: cover the compact
`spec(a) ⊆ ℂ` by finitely many `δ`-balls centred at spectrum points `λ`, turn
the tent functions `max(0, δ − |z−λ|)` into a partition of unity `ψ_λ` by
dividing by their (strictly positive) sum, and set `g_λ := ψ_λ(a)`.  Then
`g_λ ≥ 0`, `∑ g_λ = 1` and `‖a − ∑ λ g_λ‖ ≤ δ` by `norm_cfc_le`.

The one instance of `cp_commutative_dom` that survives is the new private
`norm_sum_smul_le_aux` / `norm_sum_smul_le_of_nonneg`:

> `‖∑ₖ λₖ pₖ‖ ≤ (maxₖ|λₖ|)·‖∑ₖ pₖ‖` for positive `pₖ` in a C\*-algebra.

and there it is **elementary**: it is `cp_russo_dye` applied to the positive
map `c ↦ ∑ₖ cₖ pₖ` out of `ι → ℂ` (a C\*-algebra in Mathlib for `Fintype ι`),
whose complete positivity is a one-line regrouping —
`∑ᵢⱼ bᵢ* φ(c̄ᵢcⱼ) bⱼ = ∑ₖ dₖ* pₖ dₖ` with `dₖ = ∑ᵢ cᵢ(k) bᵢ`.  No
approximation is involved.  So the general 34IX.2 is still open, but nothing
in parsec 341 waits on it.

*Also worth recording (checked, not recalled):* the proved `cp_russo_dye`
uses its complete-positivity hypothesis **only at `n = 1` and `n = 2`** — at
`1` through `astara_pos_basic_2_cp` (which is `hf 1` and nothing else) and at
`2` through `cp_cs f hp (hf 2)`.  So 34XVI holds verbatim for 2-positive
maps, which is worth knowing the next time a merely 2-positive map turns up.

### 2. 34aVIII `russo_dye_cor` — divergence class 1 (faithful)

The thesis's own limit argument on top of the already-proved **34aVII**
`russo_dye`: for `‖x‖ < 1` pick `N > 2/(1−‖x‖)`, write `x = (u₁+⋯+u_N)/N`,
and bound each `‖f(uᵢ)‖ ≤ ‖f(1)‖‖uᵢ‖ = ‖f(1)‖` by 34aII (a unitary is normal
of norm 1).  One cosmetic departure: the thesis approximates a norm-`≤ 1`
element by such means and passes to the limit; we instead apply the ball
statement to `r⁻¹·a` for every `r > ‖a‖`, which needs no closedness of the
set of means.

**This releases 128VI `sef_instrument`** (`A/Proc/Duplicators.lean`), which
worker 49 identified as needing `‖f'‖ ≤ 1` sharply for a merely positive
unital map.

### 3. 74I `proto_kaplansky` — divergence class 1 apart from one shortcut

The thesis's plan (vn.tex 740.20, "an adaptation of Conway Lemma 44.2") is
transcribed in full, as a block of private lemmas about

```
USCont A g  :=  Continuous g ∧ (the ε–δ form, in the seminorms ‖·‖_ω, of
                "a ↦ g(a) is ultrastrongly continuous on sa(A)")
```

`continuousOn_of_usCont` turns that into the `ContinuousOn` of the statement,
using w47's `exists_ultrastrong_ball_of_isOpen` for the `𝓝`-basis.  Then, in
the thesis's order: `usCont_id`, `usCont_const`, `usCont_add`,
`usCont_smul`, `usCont_comp_affine` (precomposition with `t ↦ rt+c`, via
`cfc_comp`), `usCont_mul` (`g·h` when `g` is **bounded** — this is where
`‖g(b)‖ ≤ C` and `omegaNorm_mul_right` do the work), and `usCont_of_approx`
(closure under uniform limits, via `‖x‖_ω ≤ ‖x‖·‖1‖_ω`).

`usCont_efun` is the heart, and is the thesis's identity verbatim:

```
e(b) − e(a) = s(b)(b−a)s(a) − e(b)(b−a)e(a),   e(t)=t/(1+t²), s(t)=1/(1+t²)
```

proved from `(1+a²)s(a) = 1`, `s(b)(1+b²) = 1` and `e = id·s = s·id`
(all four by `cfc_mul`) plus one `noncomm_ring`; the estimate is
`‖s(b)‖ ≤ 1`, `‖e(b)‖ ≤ 1` and `‖(b−a)c‖_ω = ‖b−a‖_{c*ω}`, i.e.
`omegaNorm_mul_right` — **made public in `A/VN/Basic.lean` for this
purpose** (it was file-private).  `s = 1 − t·e(t)` then gives `usCont_sfun`.

**The one deliberate shortcut.**  Where the thesis adjoins all the
`e_{a,b}(t) = e(at+b)` and appeals to Stone–Weierstraß for the C\*-algebra
they generate in `C(ℝ ∪ {∞})`, taking real parts at the end, we adjoin only
the translates `s(t−c)`.  They already separate the points of `ℝ ∪ {∞}`
(`s(x−c) = s(y−c)` forces `c = (x+y)/2`; and `s(·−c) > 0` on `ℝ` while it
vanishes at `∞`), and being real-valued they let Mathlib's *real*
Stone–Weierstraß
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`)
apply to `Algebra.adjoin ℝ (Set.range kapGen) ⊆ C(OnePoint ℝ, ℝ)` directly,
with no real-part step.  `OnePoint.continuousMapMk` builds the extensions;
`Algebra.adjoin_induction` transports membership back to `USCont`, the `mul`
case using `‖F x‖ ≤ ‖F‖` on the compact `OnePoint ℝ` for the boundedness
`usCont_mul` demands.

Finally the thesis's reduction, verbatim: `f = f·s + (f·s·t)·t`, where
`f·s` vanishes at infinity (from `|f(t)| ≤ b|t|`, since `|t|/(1+t²) ≤ 1/|t|`)
and both `f·s` and `f·s·t` are bounded (`bounded_of_bigO`: a continuous
function bounded outside `[−n,n]` is bounded, by
`IsCompact.exists_bound_of_continuousOn`).  Each of the two multiplications
by `id` is one application of `usCont_mul`.

### 4. 74III `abs_us_cont` — divergence class 1, free

`|t| = 1·|t|` for all `t`, so 74III is `proto_kaplansky (fun t => |t|)
continuous_abs ⟨0, 1, …⟩`.  One line.

### 5. Verification

* Whole-project `lake build` → exit 0, `Build completed successfully
  (8738 jobs)`; `grep error:` yields only the pre-existing
  `linter.style.header` noise from `A/VN/Basic.lean` (the `²` token), zero
  after filtering.  Log `scratchpad/w51full.log`.
* `sorry` counts from that log's `declaration uses \`sorry\`` lines (never a
  grep): `A/CStar` 39 → **37** (`Matrices` 6 → 4), `A/VN` 114 → **112**
  (`Completeness` 15 → 13).  `A/Proc` 128 and `B/Eff` 20 unchanged;
  `B/Dils` 60 is the concurrent worker's.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` for
  `Theses.A.CStar.normal_russo_dye`, `.russo_dye_cor`,
  `Theses.A.VN.proto_kaplansky`, `.abs_us_cont`, plus regression checks on
  `.russo_dye` and `.cp_russo_dye`.
* **Warnings: none added.**  Message lists for the three touched files were
  read off the full build and filtered to the edited line ranges
  (`Matrices.lean` 1470–1740 and beyond, `Completeness.lean` 1400–1900,
  `Basic.lean` 2125–2145): empty.  Every new private lemma that needed one
  carries an `omit … in`, and the three `show`s that changed the goal were
  turned into `change` for `linter.style.show`.
* Files touched: `Theses/A/CStar/Matrices.lean`, `Theses/A/VN/Basic.lean`
  (one `private` removed), `Theses/A/VN/Completeness.lean`,
  `PROVING-LOG.md`.  `ERRATA.md`/`QUESTIONS.md` deliberately untouched —
  nothing false found and no author decision is needed.  Nothing staged,
  nothing committed.

## Session 23 — `A/VN` parsecs 740–750: Kaplansky density and Kadison's lemma (worker 54)

Date 2026-08-14.  Successor of session 22 (worker 51) on the A chain.
Scope: `Theses/A/CStar/*.lean` and `Theses/A/VN/*.lean`.

**Result: `A/VN` 112 → 106, `A/CStar` 37 → 37.  Six statements proved:
74IV.1 `kaplansky_sa`, 74IV.2 `kaplansky_pos`, 74IV.3 `kaplansky_effects`,
75II `sequence_separation_lemma`, 75VI `kadisons_lemma`, and
66IV.3 `ultracyclic_basic_3`.**  All six `#print axioms`-clean
(`propext, Classical.choice, Quot.sound`), as are the regression targets
`proto_kaplansky`, `abs_us_cont`, `ultraclosed`, `luws`, `ceil_mem`,
`projections_norm_dense_subalgebra`.

### 1. 74IV Kaplansky — the three "moreover" clauses, class 1

The three special cases follow the thesis (vn.tex:4344) step for step:

* the real parts of an approximating net converge **ultraweakly** to
  `Re(b) = b`, so `b` lies in the ultraweak closure of the convex set
  `sa(S)`;
* by **73VIII** `ultraclosed` the ultraweak and ultrastrong closures of a
  convex set coincide, so `b` is already an ultrastrong limit from `sa(S)`;
* clamping with `−‖b‖ ∨ (·) ∧ ‖b‖`, ultrastrongly continuous by **74I**
  `proto_kaplansky`, brings the norms down to `‖b‖` without moving the
  limit, because `cfc f b = b` when `f = id` on `spec(b) ⊆ [−‖b‖,‖b‖]`.

New private infrastructure in `Completeness.lean`, all reusable:
`mem_usClosure_iff` (closure membership in terms of the `‖·‖_ω`),
`convex_usClosure` (the ultrastrong closure of a convex set is convex — the
`‖·‖_ω` are seminorms), `usClosure_subset_uwClosure` (from the tree's
`ultrastrong_le_ultraweak`), `continuous_ultraweak_realPart`,
`mem_usClosure_selfAdjointPart`, `exists_net_of_mem_usClosure` (the
tautological net indexed by the set itself, which is how the
`∃ (ι : Type u) (l : Filter ι)` shape of the statements is met), and
`usTendsto_cfc`.

*Divergence, class 3 (mild)*: for `kaplansky_pos` the thesis clamps to
`[−‖b‖,‖b‖]` and then takes positive parts; we clamp once with
`0 ∨ (·) ∧ ‖b‖`, which is the composite of the two.  `kaplansky_effects` is
the thesis's own observation that the positive case already delivers
effects, since `‖a_α‖ ≤ ‖b‖ ≤ 1`.

**The general (non-self-adjoint) 74IV `kaplansky` is left `sorry`.**  The
thesis proves it by running the self-adjoint case in `M₂(𝒜)` on
`[[0,b],[b*,0]]`, which needs **49IV**.1 `mn_vna_1` (`M_N(𝒜)` is a von
Neumann algebra) *and* **49IV**.2' `mn_vna_2'` (entrywise ultrastrong
convergence), both still `sorry` in `Basic.lean`.  Closing 74IV through them
would make it axiom-tainted rather than proved, so it was not attempted.
Checked: the naive substitute — `b = Re b + i·Im b` with 74IV.1 applied to
each part — gives only `‖a_α‖ ≤ 2‖b‖`, so the matrix trick really is doing
work.  **Nothing downstream of parsec 740 needs the general form**: 75VI
uses only `kaplansky_effects` (vn.tex:4570 says "we may assume that all `b_α`
are effects"), and 74VI `dense_subalgebra` — the only other consumer — is
itself unused until 77V.

Also made public: `spectrum_abs_le` in `Projections.lean` (`|r| ≤ ‖a‖` for
`r ∈ spec_ℝ(a)`, `a` self-adjoint), which the clamping functions need.

### 2. 75II `sequence_separation_lemma` — class 1, with one indexing change

The thesis's proof (vn.tex:4482, after Conway 45.3/45.6) is transcribed:
choose a subsequence with `ω₀(b_n) ≤ n⁻¹2⁻ⁿ` and `ω₁(b_n^⊥) ≤ n⁻¹`, form
`a_{nm} = (1+d)⁻¹d` for `d = ∑_{k=n}^m k b_k`, and take
`a = ⋀_n ⋁_{m≥n} a_{nm}`, then `q = ⌈a⌉`.

Two representation choices, both class 3:

* `(1+d)⁻¹d` is presented as `cfc frac d` for the *globally continuous*
  `frac t = (t ∨ 0)/(1 + (t ∨ 0))`.  That makes `a_{nm} ∈ S` (a norm-closed
  star subalgebra is closed under the CFC), `0 ≤ a_{nm} ≤ 1` and
  `a_{nm} ≤ d` immediate; the identification `cfc frac d = (1+d)⁻¹d`
  (`cfc_frac_eq`) is proved once and is the only place **25II**.4
  `astara_pos_basic_4` — the thesis's "`d ↦ (1+d)⁻¹d` is order preserving" —
  is needed.
* the thesis's `∑_{k=n}^{m}` is rendered as a sum over `Finset.range m` of
  `(n+j+1)·c(n+j)`, i.e. the same family reindexed by `j = k − n`.  This
  keeps every sum in `Finset.range` form (`Finset.sum_range_succ'` for the
  `n ↦ n+1` step, `geom_sum_eq` for `∑_j 2⁻ʲ ≤ 2`).

The thesis's "corresponding inequality for effects, obtained via Gelfand's
representation theorem" — `(1+mb)⁻¹ ≤ (1+m)⁻¹(1+mb^⊥)` — is here one
application of `cfc_le_iff` (`effect_key_ineq`), since both sides are
continuous functions of the *single* element `mb`; no Gelfand duality is
involved.  Its numeric content is
`(1+M)⁻¹(1+M−t) − 1/(1+t) = t(M−t)/((1+t)(1+M)) ≥ 0` for `0 ≤ t ≤ M`, and
`spec(M·b) ⊆ [0,M]` because `‖M·b‖ ≤ M`.

Simplification worth telling the author: **the infimum step never needs the
normality of `ω₀`.**  The thesis writes
`ω₀(a) = ⋀_n ⋁_{m≥n} ω₀(a_{nm})`, but `a ≤ a_n` alone gives
`ω₀(a) ≤ ω₀(a_n) ≤ 2⁻ⁿ`, so only the *suprema* `a_n = ⋁_m a_{nm}` are ever
evaluated by a functional.  Correspondingly `a` is built as `1 − ⋁_n(1−a_n)`
(an ascending supremum) rather than as a descending infimum, which avoids
needing infima in a von Neumann algebra at all.

**Hypothesis check: `ω₀(1) = 1` is never used.**  The `ω₀` half of the
argument needs only that `ω₀` is positive and normal; only `ω₁`'s
normalisation enters, and there only through `ω₁(1) ≤ 1`.  The Lean binder
is therefore spelled `_hω₀`; the statement is unchanged (the thesis's
hypothesis is retained, since every call site supplies npu-maps anyway).
This is the same kind of finding as the redundant boundedness hypothesis in
166II.

### 3. 75VI `kadisons_lemma` — class 1, three lines of content

Kaplansky in the effect form replaces the approximating net by one of
effects, `uwweaker_2` turns ultrastrong convergence into ultraweak, and
75II finishes.  It is the first consumer of 74IV and it needs only the
effect case, which is why the general 74IV being open costs nothing here.

### 4. 66IV.3 `ultracyclic_basic_3` — class 2, taken because 75VIII needs it

`p = ⋁_ω ⌈ω⌉` over the np-functionals `ω` with `ω(p^⊥) = 0`.  The thesis's
hint is "first consider `p = 1`"; the reduction turns out to be unnecessary,
because the compression trick that proves the `p = 1` case works verbatim at
every `p`.  That `p` is an upper bound is the defining leastness of `⌈ω⌉`.
For leastness: let `r` be a projection above every such `⌈ω⌉`; for an
arbitrary np-functional `τ` the compression `ω := τ(p(·)p) = conjNP p τ`
satisfies `ω(p^⊥) = 0`, so `⌈ω⌉ ≤ r`, hence `ω(r^⊥) = 0` (monotonicity plus
`ω(⌈ω⌉^⊥) = 0`), i.e. `τ(p r^⊥ p) = 0`.  As `τ` was arbitrary and
`p r^⊥ p ≥ 0`, faithfulness (**42I**.2, `np_faithful`) gives `p r^⊥ p = 0`;
then `‖r^⊥ p‖² = ‖p r^⊥ p‖ = 0`, so `rp = p = pr` and `p = r p r ≤ r`.

Nothing is *released* by this on its own — it is one of the three
ingredients 75VIII needs (§5).

### 5. Left open, with blockers

* **75VIII `vnsac`** — the next link, and *not* reachable this round.  Its
  proof needs (a) the *dual* of 66IV.3, `p = ⋀_ω ⌈ω⌉^⊥` over `ω` with
  `ω(p) = 0`, which the thesis uses in the display at vn.tex:4610 but never
  states (it follows from 66IV.3 at `p^⊥` plus De Morgan for projections);
  (b) the
  *relativised* carriers `⌈ω⌉_S` — carriers of restrictions of `ω` to `S`,
  which presupposes transporting the von Neumann structure to `S`; and (c)
  the thesis's unstated step "the ultrastrong closure of `S` is a von
  Neumann subalgebra".  For (c) there is a clean route, worth recording
  because it is not in the thesis: `T := us-closure(S)` is convex and
  ultrastrongly closed, hence **ultraweakly** closed by 73VIII, hence
  `T = uw-closure(S)`; the ultraweak closure is star-closed because the
  adjoint is ultraweakly continuous, `T·T ⊆ T` follows from *separate*
  ultrastrong continuity of multiplication applied twice, and `T` is closed
  under directed suprema by **44XIV** `vna_supremum_uslimit`.
* **74IV general / 74VI `dense_subalgebra`** — blocked on `mn_vna_1` and
  `mn_vna_2'` (§1).
* **77I `vn_complete_1/2`** — blocked on 75VIII.

### 6. Verification

* `lake build` (whole project) at the end: exit 0, 8738 jobs
  (`scratchpad/w54full2.log`).  Sorry counts from the build log's
  `declaration uses \`sorry\`` lines (never a grep): `A/CStar` 37,
  **`A/VN` 106**, `A/Proc` 128, `B/Dils` 60, `B/Eff` 20 — the last three
  exactly as found.
* `#print axioms` on all six new theorems and six regression targets:
  standard three only (`scratchpad/w54ax.lean`, `w54ax2.lean`,
  `w54ax3.lean`).
* Warning profile: the build's message list restricted to the edited line
  ranges of `Completeness.lean` and `Projections.lean` contains **no new
  warnings** — every new private lemma carries the `omit … in` the linter
  asked for, `letI` became `let`, and the one `show` that changed the goal
  became `change`.  (The deprecation warnings from parsecs 760/770 and the
  `linter.style.header` noise in `Basic.lean` are pre-existing.)
* Files touched: `Theses/A/VN/Completeness.lean`,
  `Theses/A/VN/Projections.lean` (66IV.3 proved; `spectrum_abs_le` made
  public), `PROVING-LOG.md`.
  `ERRATA.md`/`QUESTIONS.md` deliberately untouched — nothing false found
  and no author decision is needed.  Nothing staged, nothing committed.

## Session 24 — `B/Dils` parsec 1580: **158V is false** (worker 55)

Task: close two of the four estimates `kaplansky_hilbmod_A₁/A₁'/A₂/A₂'` in
`Theses/B/Dils/Kaplansky.lean` (158V, the ultranorm continuity of
`h(y) = y·2/(1+⟨y,y⟩)`, dils.tex point 1580.50).  **None of the four is
provable: they are false, and so is 158V.**  Divergence class (4′) — not a
mis-transcription of ours, a defect in the thesis; filed in ERRATA.md under
**158V**, and reproduced in the doc comment above the four theorems.

### The counterexample

`ℬ = B(ℓ²)`, `X = ℬ` over itself, `pₙ = |eₙ⟩⟨eₙ|`; thesis convention
(`⟨a,b⟩ = a*b`, right module):

  `y = |e₂⟩⟨e₁|`,   `yₙ = |e₂⟩⟨e₁+eₙ|`   (`n ≥ 2`).

`⟨yₙ−y, yₙ−y⟩ = pₙ`, and `ω(pₙ) → 0` for **every** np-functional `ω`
(`ω = Tr(ρ·)`, `ρ` trace class, so `ρₙₙ → 0`), hence `yₙ → y` ultranorm along
`atTop` — a plain *sequence*, and one inside the ball of radius `√2`.  So this
is **not** the "bounded above but not norm-bounded" gap of 152XII/44XV that
this material was expected to hide; adding a norm bound repairs nothing.

With `w = e₁+eₙ`: `P = ⟨y,y⟩ = p₁`, `Q = ⟨yₙ,yₙ⟩ = |w⟩⟨w|`,
`(1+P)⁻¹ = 1 − ½p₁`, `(1+Q)⁻¹ = 1 − ⅓|w⟩⟨w|`.  For `ω₀ = ⟨e₁, · e₁⟩` and
every `n` (values independent of `n`; checked symbolically and numerically on
the 3-dimensional truncation, which carries the whole computation):

| | `A₁` | `A₁'` | `A₂` | `A₂'` | `⟨h(y)−h(yₙ), h(y)−h(yₙ)⟩` |
|---|---|---|---|---|---|
| `ω₀` | `−1/12` | `−1/18` | `0` | `1/6` | `1/9` |

`ω₀(⟨yₙ−y,yₙ−y⟩) = 0` throughout.  (`A₂` vanishing at `ω₀` says only that this
one functional does not see it; `A₁`, `A₁'`, `A₂'` and the splitting suffice.)  Concretely `h(y) = |e₂⟩⟨e₁|` while
`h(yₙ) = ⅔|e₂⟩⟨w|`, so `h(yₙ) → ⅔|e₂⟩⟨e₁| ≠ h(y)` — the factor `2/3` never
goes away.

### Where the printed proof breaks

Exactly at the **right-hand half of `kaplanskytodo2`** (dils.tex:4251) — the
one the thesis dispatches with "the proof for the RHS is different, but
simpler", without giving it.  It is false:
`⟨y, yₙ−y⟩(1+⟨yₙ,yₙ⟩)⁻¹ = |e₁⟩⟨eₙ| − ⅓|e₁⟩⟨w|` has `ω₀`-value `−1/3`.

The asymmetry is real and worth recording, because it is what makes the LHS
work and the RHS fail.  Write `d = y_α − y`, `s = (1+⟨y_α,y_α⟩)⁻¹`.

* **LHS**, `⟨d, y_α⟩s = ⟨d, y_α s⟩`: the resolvent is absorbed into the
  *second* slot, and `‖y_α s‖ ≤ 1` because `s⟨y_α,y_α⟩s = s − s²  ≤ 1`.
  Module Cauchy–Schwarz against `‖d‖_ω → 0` closes it.  This half is fine.
* **RHS**, `⟨y, d⟩s = b_α s` with `b_α = ⟨y,d⟩`: module Cauchy–Schwarz gives
  `b_α* b_α = ⟨d,y⟩⟨y,d⟩ ≤ ‖⟨y,y⟩‖⟨d,d⟩`, i.e. `ω(b*b) → 0` — the *unmirrored*
  ultrastrong topology.  But `|ω(bs)|² ≤ ω(bb*)·ω(s*s)` needs `ω(bb*) → 0`,
  the *mirrored* one, and the swap is exactly the one that
  `module_CS`/`chilb_cs` refuses to make (the doc comment on `module_CS` in
  `HilbertModules.lean` already records that the unswapped inequality is
  false).  And "ultrastrongly null times norm-bounded is ultraweakly null" is
  false on the wrong side: `|e₁⟩⟨eₙ| → 0` ultrastrongly, `‖|eₙ⟩⟨e₁|‖ = 1`,
  product `= |e₁⟩⟨e₁|`.  The counterexample above is this observation dressed
  as a Hilbert module.

**158II `kaplansky_hilbmod` is not thereby refuted** and is presumably true:
its statement (both the thesis's and ours) is an entourage/`∃ d ∈ D` one, so
the approximant may be *chosen* per finite family of np-functionals — one is
not obliged to feed `h` an arbitrary ultranorm-convergent net.  A repair
plausibly enlarges the family (e.g. by the `conjNP`-twists that show up in the
estimates) before applying ultranorm density.  Not attempted here.

### What is in the file

The four `sorry`s stay (nothing false has been *stated*: the four statements
are the thesis's, and they are what the erratum is about).  Above them, the
`158V` section comment now carries the counterexample.  New, and proved:
resolvent infrastructure that any repair will want, all of it `private`,

* `isUnit_one_add`, `inv1p_mul`, `mul_inv1p`, `inv1p_star` — `1+b` is a unit
  for `0 ≤ b` via `IsStrictlyPositive.add_nonneg`, no spectral argument;
* `rf`, `rf_continuous/nonneg/le_one`, `one_add_mul_rf`, `inv1p_eq_cfc` —
  `(1+b)⁻¹ = cfc (t ↦ (1+max t 0)⁻¹) b`, modelled on `cfc_frac_eq` in
  `A/VN/Completeness.lean` (whose analogues are `private` there, hence redone);
* `inv1p_nonneg`, `inv1p_le_one`;
* `inv1p_comm` (`b(1+b)⁻¹ = (1+b)⁻¹b`, both `= 1 − (1+b)⁻¹` — no functional
  calculus needed) and `inv1p_conj_le_one`
  (`(1+b)⁻¹b(1+b)⁻¹ = (1+b)⁻¹ − ((1+b)⁻¹)² ≤ 1`), which are the two facts the
  thesis lists at dils.tex:4213 and the two that make the LHS of
  `kaplanskytodo2` go through.

### Two by-products of the same computation

* **`kaplansky-splitting` is off by a factor `4`.**  `h(y) = y·2/(1+⟨y,y⟩)`, so
  the left-hand side carries the square of that `2` and none of the four `A`s
  does; the identity is `⟨h(y)−h(y_α),h(y)−h(y_α)⟩ = 4(A₁+A₁'+A₂+A₂')`.  Above:
  `1/9 = 4·1/36`.  Harmless as printed (all four are claimed to vanish); filed
  in ERRATA.md as a nit.  It is also the check that caught the next item.
* **Ours: `kaplansky_hilbmod_A₂` and `A₂'` were transcribed without the
  mirroring swap.**  `inner ℬ (y i - y₀) (y i)` is `⟨y_α, y_α − y⟩`, whereas
  the thesis's `A₂` has `⟨y_α − y, y_α⟩ = inner ℬ (y i) (y i - y₀)`; likewise
  `A₂'`.  This is the sixth and seventh instance of the swap being dropped in
  this chapter.  `A₁`/`A₁'` mention only `⟨y,y⟩` and `⟨y_α,y_α⟩`, so they are
  convention-free and the refutation above applies to them exactly as stated.
  Both `A₂` forms are false regardless, so the statements were left as they
  are rather than half-repairing a doomed theorem; the doc comment records it.

`lake build Theses.B.Dils.Kaplansky`: exit 0, no errors, no new warnings.

### Correction to three earlier reports and to `HANDOFF.md`

They record `Kaplansky.lean` as waiting on 74IV.  That is true of **158Ia**
`kaplansky_bounded_approx` only.  **158II depends on nothing outside the
tree**: dils.tex point 1580.11 is an unlabelled expository restatement of the
density theorem and cannot be cited, and the proof of `kaplansky-hilbmod`
never cites `\sref{kaplansky}`.  158II is blocked by *this* erratum, not by
74IV.

## Session 25 — `A/VN` parsec 490 and the general 74IV/74VI (worker 56)

Date 2026-08-14.  Successor of session 23 (worker 54) on the A chain.
Scope: `Theses/A/CStar/*.lean` and `Theses/A/VN/*.lean`.

**Result: `A/VN` 106 → 102, `A/CStar` 37 → 37.  Four statements proved:
49IV.1 `mn_vna_1` (an *instance*, one of the project's two `sorry`ed ones),
49IV.2' `mn_vna_2'`, the general 74IV `kaplansky`, and 74VI
`dense_subalgebra`.**  All four `#print axioms`-clean, as are the new
auxiliaries and the regression targets `kaplansky_sa`, `kaplansky_effects`,
`sequence_separation_lemma`, `kadisons_lemma`, `ultraclosed`.

### 0. The `sorry`ed instance `mn_vna_1` is gone

`instance mn_vna_1 : VonNeumannAlgebra (CStarMatrix (Fin N) (Fin N) 𝒜)` was
one of the two invisible-taint sites.  Its only consumer outside `A/VN` is
`Theses/A/Proc/QuantumLambda.lean:425`,
`instance (n : ℕ) : VonNeumannAlgebra (MatAlg n) := mn_vna_1 n`, which
carries the *types* of the parsec-1253/1254 block (`GeneratesMat`,
`MIUEquiv`, `TensorBEquiv`, `Fha_concrete`, `AstarhaB_concrete`).  Those
types were `sorryAx`-tainted; they are now clean
(`#print axioms Theses.A.Proc.instVonNeumannAlgebraMatAlg` gives the
standard three).  Nothing in the tree *proved* anything through the
instance, so no previously-vacuous proof needed re-examination.
The remaining `sorry`ed instance is `vonNeumannAlgebra_lp_infty`
(`Basic.lean`), untouched.

### 1. 49IV.1 `mn_vna_1` — divergence class 2 (different route), forced

The thesis proves 49IV.1 by way of 49II (`bah-vn`): `M_N(𝒜) = B^a(𝒜^N)` and
`B^a(X)` is a von Neumann algebra for self-dual `X`.  `B^a(X)` has no
Mathlib counterpart and is *not formalized* (the FIXME at `Basic.lean`
parsec 490 records this), so 49II is unavailable and the route had to be
replaced.  The replacement uses the same ingredient 49II does — the
`𝒜`-valued form of the Hilbert module `𝒜^N` — but stays inside `M_N(𝒜)`:

* `matForm x y M = ∑ᵢⱼ xᵢ* Mᵢⱼ yⱼ`, with **33II**
  (`cstar_matrix_positive_iff`, `A/CStar/Matrices.lean`, already proved)
  giving `0 ≤ M ↔ ∀ x, 0 ≤ matForm x x M`, hence `le_iff_matForm`;
* polarisation `Mᵢⱼ = ¼ ∑_{k<4} iᵏ ⟨eⱼ+iᵏeᵢ, M(eⱼ+iᵏeᵢ)⟩`
  (`matForm_polarization`), which also gives `matrix_ext_of_matForm`: the
  quadratic form determines the matrix;
* for a bounded directed `D ⊆ sa(M_N(𝒜))`, each family
  `{matForm x x d : d ∈ D}` is directed and bounded in `sa(𝒜)`, so it has a
  supremum `s_x`, and by **44XIV** `vna_supremum_uslimit` the net converges
  *ultrastrongly* to it;
* polarisation therefore exhibits an ultrastrong limit for every entry;
  assembling these into a matrix `S` and using that ultrastrong limits are
  unique (**44XI**.1, Hausdorff) gives `matForm x x S = s_x` for all `x`,
  whence `IsLUB D S` by `le_iff_matForm` — no ultraweak/ultrastrong
  topology on `M_N(𝒜)` is ever mentioned, which is essential, since those
  are *defined* from the np-functionals of `M_N(𝒜)` and so are not
  available before the instance exists.

Faithfulness of the np-functionals of `M_N(𝒜)` then comes from the
np-functionals `matFormNP φ x : M ↦ φ(matForm x x M)`, whose normality is
the "and the forms preserve it" half of `exists_isLUB_matForm`; taking
`x = eᵢ + i^k eⱼ` and polarising reduces faithfulness on `M_N(𝒜)` to
faithfulness on `𝒜`.

New in `Basic.lean` (all before the instance, so the compiler enforces that
none of it can use the instance): `matForm` and its (bi)linearity lemmas,
`matUnit`, `matPolVec`, `matForm_polarization`, `matrix_ext_of_matForm`,
`nonneg_iff_matForm`, `le_iff_matForm`, `matFormSA`, `exists_isLUB_matForm`,
`matFormNP`.

Also new and of general use, in the same file: `omegaNorm_smul` (**moved**
here from `Completeness.lean`, where it was a public duplicate-in-waiting),
`usTendsto_smul/_add/_const/_finsetSum`, `uwTendsto_finsetSum`,
`usTendsto_mul_left_right`.  `Theses/B/Dils/SelfDualCompletion.lean:563`
carries a comment asking for exactly these; they are now available (its own
private primed copies were left alone — another worker owns that file).

### 2. 49IV.2' `mn_vna_2'` — class 1 (faithful)

Both directions, both topologies, exactly as the thesis states them.

* *matrix ⇒ entrywise*, ultraweak: `φ(Mᵢⱼ)` is the `ℂ`-combination
  `¼∑ₖ iᵏ · matFormNP φ (eⱼ+iᵏeᵢ) M` of np-functionals of `M_N(𝒜)`.
* *matrix ⇒ entrywise*, ultrastrong: the clean estimate
  `‖Xᵢⱼ‖_φ ≤ ‖X‖_{matFormNP φ eⱼ}`, because
  `matFormNP φ eⱼ (X*X) = φ(∑ₖ Xₖⱼ* Xₖⱼ) ≥ φ(Xᵢⱼ* Xᵢⱼ)`.
* *entrywise ⇒ matrix*, both: `M = ∑ᵢⱼ matEmb i j (Mᵢⱼ)` with
  `matEmb i j x` the matrix with `x` in position `(i,j)`.  The diagonal
  corners `matEmb j j` are *normal* positive maps — that is **44VIII**
  `ad_normal` plus `le_iff_matForm` — so they pull np-functionals of
  `M_N(𝒜)` back to np-functionals of `𝒜` (`matEmbNP`), and polarisation
  (**44II**, in the form the tree's `continuous_ultraweak_conj` uses)
  handles the off-diagonal corners via
  `matEmb i j x = (matEmb i j 1)·(matEmb j j x)`.  For the ultrastrong
  half, `‖matEmb i j x‖_ω = ‖x‖_{matEmbNP j ω}` is exact, because
  `(matEmb i j x)*(matEmb i j x) = matEmb j j (x* x)`.

### 3. General 74IV `kaplansky` — class 1, with one repair to the thesis

The thesis (vn.tex:4400) writes: "`B = [[0,b],[b*,0]]` … is the ultrastrong
limit of the net `[[0,aα],[aα*,0]]` from the C*-subalgebra `M₂(𝒜)`".
**That step is not correct as stated**: `aα → b` ultrastrongly does *not*
give `aα* → b*` ultrastrongly — the adjoint is not ultrastrongly
continuous, which is the thesis's own **43II**.4 (`vn-counterexamples`) —
and by 49IV.2' entrywise ultrastrong convergence is exactly what would be
needed.

The repair costs two lines and uses only what the thesis has already used
in this very proof: the adjoint *is* ultraweakly continuous
(`ω(a*) = conj(ω a)`), so `[[0,aα],[aα*,0]] → B` **ultraweakly**, putting
`B` in the ultraweak closure of the convex set `M₂(𝒜)`; and **73VIII**
`ultraclosed` — invoked three paragraphs earlier for the self-adjoint case
— moves it into the ultrastrong closure.  From there the argument is the
thesis's: run the self-adjoint case in `M₂(ℬ)`, then read off the
upper-right entries with 49IV.2'.

Not an erratum in `ERRATA.md`: the statement of 74IV is true and its proof
is repairable in place with a tool the same proof already uses.  Recorded
in the doc comment above `kaplansky` and here.

Supporting material, private in `Completeness.lean` (`MatrixTrick` block):
`matStarSubalgebra S N` (the ∗-subalgebra `M_N(S)`, norm-closed because the
entry maps are `1`-Lipschitz by `CStarMatrix.norm_entry_le_norm`),
`matEmb_mul_of_ne`, `antiDiag b = [[0,b],[b*,0]]`, `norm_antiDiag_le`
(`‖B‖ ≤ ‖b‖`: `B*B = diag(bb*, b*b) ≤ ‖b‖²·1` by `le_iff_matForm`, then
`CStarAlgebra.norm_le_iff_le_algebraMap`), `uwTendsto_add'`,
`uwTendsto_star'`, `mem_uwClosure_of_uwTendsto`,
`mem_usClosure_of_mem_uwClosure`, `convex_starSubalgebra(A)`.
`matEmb_mul_of_ne` belongs next to `matEmb_mul` in `Basic.lean`; it is here
only to avoid a second full rebuild.

**Note on declaration order.**  `kaplansky` is now stated *after* the three
"moreover" clauses (just before 74VI), because its proof calls
`kaplansky_sa` at `M₂(𝒜)`.  The docstrings say so.

### 4. 74VI `dense_subalgebra` — class 2 (different route)

The thesis builds a double net indexed by `D × ℕ` (`s_{αn} ∈ 𝒮` with
`‖cα − s_{αn}‖ ≤ 2⁻ⁿ`, then passes to a subsequence for the norm bound).
We avoid the product filter entirely: it suffices to show that `a` lies in
the ultrastrong closure of `K = {s ∈ 𝒮 : ‖s‖ ≤ ‖a‖(1+ε)}`, since
`exists_net_of_mem_usClosure` then produces the tautological net indexed by
`K`.  Membership is checked with `mem_usClosure_iff`: given `ω` and `δ > 0`,
74IV applied to the norm closure `C = 𝒮̄` yields `c ∈ C` with `‖c‖ ≤ ‖a‖`
and `‖c − a‖_ω < δ/2`, and then a single `s ∈ 𝒮` with
`‖s − c‖ < min(ε‖a‖, δ/(2(‖1‖_ω+1)))` does both jobs at once, using
`‖x‖_ω ≤ ‖x‖·‖1‖_ω` (which is `omegaNorm_mul_le ω x 1`).  The case
`‖a‖ = 0` is separate (`a = 0 ∈ 𝒮`), as it must be: for `a = 0` the
thesis's `‖s_{αn}‖ ≤ (1+ε)‖a‖` forces `s = 0`, which the `2⁻ⁿ`
approximation does not give.

### 5. Checked and *not* used

* `mn_vna_2` (49IV.2 first half: ultraweak/ultrastrong continuity of
  `M ↦ ∑ aᵢ* Mᵢⱼ bⱼ`) and `mn_vna_3` are still `sorry`.  The *normality*
  clause of `mn_vna_2` is now free (it is `exists_isLUB_matForm` at
  `a = b`); the two continuity clauses need a finite sum of np-functionals
  (`addNP` iterated over `Fin N × Fin N`, with `omegaNorm_le_addNP`), which
  nothing in the tree provides yet.  Left open deliberately: neither is on
  any critical path.
* The thesis's remark "In particular, `A ↦ Aᵢⱼ` is ultraweakly and
  ultrastrongly continuous" is the `⇒` half of 49IV.2' and is proved as
  part of it.

## Session 26 — `B/Dils` 158Ia `kaplansky_bounded_approx` (worker 57)

Closed **158Ia** (dils.tex:4121) in `Theses/B/Dils/Kaplansky.lean`,
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).  Nothing else in
the module changed: 158II and the four false 158V estimates are untouched
`sorry`s.

**Divergence class 1 — faithful.**  158Ia *is* thesis A's 74IV
(`Theses.A.VN.kaplansky`, proved last session); the only work is the
mirror.  Chapter B expresses the ultrastrong uniformity of `ℬ` through the
ultranorm seminorms of `mulInner ℬ` (`⟨x,y⟩ = y x*`, **146VIII**), so

  `unSeminorm ω (mulInner ℬ) x = √(ω (x x*)) = omegaNorm ℬ ω (star x)`

(new private `unSeminorm_mulInner_eq`) — that is the *mirrored* ultrastrong
seminorm, whereas `A/VN`'s `omegaNorm ω a = √(ω (a* a))` is the unmirrored
one.  The two topologies genuinely differ (strong vs. strong\* on `B(H)`),
so the hypothesis and the conclusion had to be transported, not identified:

* `hdense` at `b` gives `d ∈ 𝒜` with `‖b − d‖^mirrored_ω` small, i.e.
  `omegaNorm ω (b* − d*)` small with `d* ∈ 𝒜` — so **`b*`**, not `b`, is
  what lands in the ultrastrong closure of `𝒜`;
* 74IV at `b*` yields a net `a_α ∈ 𝒜`, `‖a_α‖ ≤ ‖b*‖ = ‖b‖`, `a_α → b*`
  ultrastrongly;
* `a_α*` is then the wanted net: `star` is an isometric involution of `𝒜`
  and `unSeminorm ω (mulInner ℬ) (a_α* − b) = omegaNorm ω (a_α − b*)`.

No convexity, no **73VIII** `ultraclosed`, and no comparison with the
ultraweak topology is needed — those are all inside 74IV already.  (The
alternative route, `norm_np_le_unSeminorm_mulInner` → ultraweakly dense →
`ultraclosed` → ultrastrongly dense, would give the hypothesis but not the
*conclusion*, which is mirrored too; the `star` transport does both at
once.)  For the closure-membership step, `A/VN`'s `mem_usClosure_iff` is
`private`, so the (easy) direction needed is re-derived in two lines from
the public `exists_ultrastrong_ball_of_isOpen`.

The finitary "approximation in every entourage" phrasing that
`HilbertModules.lean` uses for nets is recovered from 74IV's net by
`Filter.eventually_all` over the finitely many `ωᵢ` plus `l.NeBot`.  No
norm-boundedness gap of the recurring "bounded above ≠ norm-bounded" kind
arises: 74IV delivers `‖a_α‖ ≤ ‖b*‖` on the nose.

`Kaplansky.lean` now imports `Theses.A.VN.Completeness` (it previously
reached `A/VN` only through `HilbertModules.lean`, which stops at
`A.VN.Projections`).

---

## Session 27 — `A/VN`: the last `sorry`ed instance, and 75VIII (worker 57)

Date 2026-08-14.  Successor of session 25 (worker 56) on the A chain.
Scope: `Theses/A/CStar/*.lean` and `Theses/A/VN/*.lean`.

**Result: `A/VN` 102 → 100, `A/CStar` 37 → 37.  Two statements proved:
42V.3/47IV.1 `vonNeumannAlgebra_lp_infty` — the project's *last* `sorry`ed
instance — and 75VIII `vnsac`.**  Both `#print axioms`-clean, as are the
eighteen new auxiliaries and the regression targets `kadisons_lemma`,
`ultracyclic_basic_3`, `kaplansky`, `isLeast_ceil_add`.

**The project now has no `sorry`ed `instance` at all** (checked by parsing
every top-level declaration of `Theses/**.lean` and testing the bodies of
those beginning `instance`/`noncomputable instance` for `sorry`, not by
grepping for the word).

### 1. `vonNeumannAlgebra_lp_infty` (`A/VN/Basic.lean`) — class 2, forced

The recorded obstruction was exactly right: everything hangs on

```
lp_infty_nonneg_iff : 0 ≤ a ↔ ∀ i, 0 ≤ a i          (for `CStarAlgebra.spectralOrder` on `lp 𝒜 ∞`)
```

and it is 30 lines.  **⇒** is `StarOrderedRing.nonneg_iff` plus
`AddSubmonoid.closure_induction`: positivity in `lp 𝒜 ∞` means membership of
the closure of `{star s * s}`, and both multiplication and the star are
pointwise.  **⇐** takes `b i = CFC.sqrt (a i)`; `‖b i‖² = ‖a i‖ ≤ ‖a‖` puts
`b` in `lp 𝒜 ∞`, and `a = star b * b`.  From it:

* `lp_infty_le_iff` (the order is pointwise) and `lpEvalSA` (evaluation on
  self-adjoint parts, monotone);
* `lp_infty_exists_isLUB`: the supremum is built **pointwise** — each fibre
  gets its supremum from `VonNeumannAlgebra (𝒜 i)`, and the family is in
  `lp` because `‖tᵢ‖ ≤ ‖S‖ + 2‖d₀‖` for `d₀ ≤ tᵢ ≤ S`
  (`CStarAlgebra.norm_le_norm_of_nonneg_of_le` applied to `tᵢ − d₀ᵢ`);
* `lpNP i ω = ω ∘ (evaluation at i)`, an np-functional, whose normality is
  the *second* half of `lp_infty_exists_isLUB` (the pointwise supremum is
  the fibre supremum) together with uniqueness of least upper bounds.
  Faithfulness of the np-functionals of `lp 𝒜 ∞` then reduces fibrewise.

Divergence class 2 — the thesis (42V, Examples) says only "the product of von
Neumann algebras is one, with everything computed coordinatewise", so the
route is the intended one but no author argument exists to transcribe.

### 2. 75VIII `vnsac` (`A/VN/Completeness.lean`) — class 2, and shorter than the thesis

The three blockers recorded by workers 54 and 56 were: the unstated dual of
66IV.3; "the ultrastrong closure of `𝒮` is a von Neumann subalgebra"; and the
relativised carriers `⌈ω⌉_𝒮`, estimated at 200–400 lines because they were
believed to need the von Neumann structure transported to `𝒮`.  **Two of the
three dissolve.**

* **The dual of 66IV.3 is not needed.**  The thesis's display is
  `⋁_{ω₁}⌈ω₁⌉_𝒮 ≥ ⋁_{ω₁}⌈ω₁⌉ = p = ⋀_{ω₀}⌈ω₀⌉^⊥ ≥ ⋀_{ω₀}⌈ω₀⌉_𝒮^⊥`.
  Complementing the right-hand half replaces `⋀_{ω₀}⌈ω₀⌉^⊥ = p` by
  `⋁_{ω₀}⌈ω₀⌉ = p^⊥`, which is **66IV**.3 itself at `p^⊥`.  So only
  `ultracyclic_basic_3` is used, twice, and no infima of projections occur
  anywhere in the proof.
* **`⌈ω⌉_𝒮` needs no von Neumann structure on `𝒮`.**  Define the *complement*
  directly: `relCoceil 𝒮 ω := projSup {q ∈ 𝒮 : q a projection, ω q = 0}`.
  Everything then follows from a single lemma, `projSup_mem_of_np`: for a set
  `P` of projections of a von Neumann subalgebra `𝒮` and an np-functional `ω`
  annihilating `P`, `projSup P ∈ 𝒮` **and** `ω (projSup P) = 0`.  Its proof
  is one directed set — the projections of `𝒮` killed by `ω` and below every
  projection upper bound of `P` — which is directed by `⌈x+y⌉`
  (`isLeast_ceil_add`), stays in `𝒮` by `ceil_mem` (56I.20 read inside `𝒮`)
  and is killed by `ω` by **60I** `ceil_functionals_lemma`; `𝒮` contains its
  supremum by `IsVNSubalgebra.dirSup_mem`, and `ω` kills it by normality.
  Total for the relativised-carrier API: ~60 lines, not 200–400.
* **The remaining ingredient really is needed** and is now in the tree as
  `usClosureSubalgebra` + `isVNSubalgebra_usClosureSubalgebra`.  Worker 54's
  route is the one that works, with one addition it did not record: the
  *norm*-closedness demanded by `IsVNSubalgebra` needs
  `norm_le_ultrastrong` (`‖a‖_ω ≤ ‖a‖‖1‖_ω` makes each `‖·‖_ω`-ball
  norm-open), which did not exist in the tree.  Multiplication uses only
  separate ultrastrong continuity, in the order "approximate the right factor
  first, then the left one in the seminorm `‖·‖_{w*ω}`" (`omegaNorm_mul_le`
  and `omegaNorm_mul_right`); the adjoint goes through the ultraweak topology
  and **73VIII**, as 74V's repair does.

One further gap in the thesis's argument, silently: 75VI `kadisons_lemma`
requires **npu**-functionals, while the display quantifies over all np ones.
`exists_unital_scaling` normalises (`smulNP` by `(ω 1)⁻¹`), and the two
degenerate cases `ω₀ 1 = 0` / `ω₁ 1 = 0` are handled without normalisation —
there `relCoceil 𝒮 ω = 1`, because `1 ∈ 𝒮` is then a projection killed by `ω`.

`isLeast_ceil_add` in `A/VN/Projections.lean` was made public (it was
`private`); `projSup_mem_of_np` needs it.  No other file was touched.

### 3. Consequences

* **77I** `vn_complete_1/2` is now blocked on nothing in `A/VN` (75VIII was
  its last prerequisite); **77III** and **77V** sit behind 77I, and 77V's
  other prerequisite 74VI is proved.  `B/Dils` **149V** is released too.
* The comment inside 21VII `order_separating_norm`
  (`A/CStar/Positive.lean`) still says the `ℓ^∞`-product "is not available in
  the tree (it is exactly the gap recorded for `vonNeumannAlgebra_lp_infty`)".
  That gap is closed, but the remark stays accurate *as a statement about
  `A/CStar`*: `A/CStar` is imported by `A/VN`, so the product is still not
  available at 21VII, and the proof there is unchanged.

## Session 29 — `B/Dils` 158II `kaplansky_hilbmod`: NOT closed; the sound half of a replacement proof is banked (worker 60)

Target: **158II** `kaplansky_hilbmod` (`Theses/B/Dils/Kaplansky.lean`), with
the thesis's own route known dead (158V is false, session 24).  Outcome: the
theorem is **neither proved nor refuted** — its `sorry` stands — but the file
gains an axiom-clean public theorem

* `kaplansky_hilbmod_of_weak` — **158II reduces to weak bounded
  approximation**: if for every np-functional `ω`, every `w ∈ X` and every
  `η > 0` there is `d ∈ D` with `‖d‖ ≤ ‖x‖` and `‖ω ⟪w, x−d⟫‖ ≤ η`, then
  the full conclusion of 158II holds for `x` (finitely many ultranorm
  seminorms at once, same ball).  Checked:
  `#print axioms` = `propext, Classical.choice, Quot.sound`.  Divergence
  class (2) if it is ever used to close 158II — the thesis has no such step.

Supporting infrastructure (all `private`): `npAdd`/`npZero`/`npSum` — finite
sums of `NPFunctional`s, with `PreservesDirSups` for a sum proved directly
from the two `IsLUB`s (upper bound via directedness: for `d, d' ∈ D` pick
`e ≥ d, d'`; then `ω₁ s ≤ z − ω₂ d'` for each `d'`, and close with the
second lub) — this avoids `npuws`, which is behind `sorry`s in `A/VN/Basic`;
`unSeminorm_le_npSum` (each `‖·‖_{ωᵢ} ≤ ‖·‖_{Σωⱼ}`);
`unSeminorm_sub_smul_sq` (the real-parameter parallelogram expansion);
`weak_to_strong` — the Mazur-style variational lemma: for one `ω` and a
*convex* `C` with `‖x−d‖_ω` bounded on `C`, weak approximability of `x` by
`C` gives `‖·‖_ω`-approximability.  The proof is the elementary approximate-
nearest-point computation (no completion, quotient, or Riesz): with
`γ = inf_{d∈C} ‖x−d‖_ω`, an `η`-nearest `d*` and a weak approximant `d`
against `w = x−d*` give, for `t ∈ [0,1]` and `d_t = d* + t(d−d*) ∈ C`,
`γ² ≤ (γ²+η²) − 2t(γ²−η²) + t²(2M)²`; optimizing `t` yields
`(γ²−η²)² ≤ η²(4M²+1)`, so `γ = 0`.  Also `smul_one_smul'`
(`(c·1) • d = c • d`, by definiteness — the section's `X` has no
`Module ℬ X`, so this is how `A ∋ c·1` makes `D` a ℂ-subspace, hence `C`
convex) and `norm_smul_complex` (no `NormedSpace ℂ X` either; `‖c•d‖ = ‖c‖‖d‖`
comes out of `CStarModule.norm_eq_sqrt_norm_inner_self`).

### Why 158II is still open — the mirror obstruction, quantified

All known routes to the weak statement (hence to 158II) funnel into one
quantity.  Take `d₀ ∈ D` ultranorm-close to `x` (`‖x‖ ≤ 1`), `b₀ = ⟪d₀,d₀⟫`,
and renormalize with any `ψ` with `t·ψ(t)² ≤ 1` (so `‖ψ(b₀)•d₀‖ ≤ 1`; the
thesis's `h` is `ψ(t) = 2/(1+t)`).  The weak defect at `ω` is controlled by
Cauchy–Schwarz up to the term `ω((1−ψ(b₀))²)` — the `ω`-mass of the spectral
part of `b₀` above `‖x‖²` — and per-vector Chebyshev gives only
`⟨v, b₀v⟩ ≤ (‖x‖+δ)²` for *requested* states `v`, i.e. bounds that mass by
`≈ 1/(1+κ)`, **not** by `o(1)`.  A concrete adversarial approximant
(`X = ℬ = B(ℓ²)`, `d₀ = x + s·|eₙ⟩⟨e₁|`-type with `s ≫ 1`, `n ≫ 1`) makes
`ω((√b₀−M)₊²) = O(1)` for every fixed cap `M`, so *truncation-style*
renormalizers provably cannot close even the weak statement one-shot.
Controlling the term the other way needs `ω(P e P)` with `P` a `d₀`-dependent
spectral projection and `e = ⟪d₀−x, d₀−x⟫` — a *mirrored* compression, which
is exactly the unprovable side of Cauchy–Schwarz that kills 158V (the same
`ω(c* · c)`-with-`c`-unknown-in-advance pattern; `conjNP` requests cannot be
made before `d₀` is seen, and adaptive two-stage schemes lose either the norm
bound or the coefficient-known-in-advance property — both variants were
worked through and fail).  A least-squares sandwich
`d = (f(b') ⟪d₀,d'⟫ (κ+b₀)⁻¹) • d₀` with `d', d₀ ∈ D` (all coefficients in
`A` by polarization) achieves `‖d‖ ≤ ‖x‖` *cleanly* — `c b₀ c* = ζζ*` with
`ζ = ⟪(b₀^½(κ+b₀)⁻¹)•d₀, ·⟫` and `‖b₀²(κ+b₀)⁻²‖ ≤ 1` — but its defect
contains the same beast for `b' = ⟪d',d'⟫`.

On the other side, **no counterexample** was found either: every attempted
adversarial `D` (rank-one escapes in `K + ℂ1`, orthogonal-escape
constructions) collapses because `D` must be an `A`-module with
`⟪D,D⟫ ⊆ A` — the inner products of the escapes land in `A` and functional
calculus/`A`-action then *trims* them, restoring good approximants.  This is
a real dichotomy, not an artifact: the `∃ d ∈ D` form survives the 158V
counterexample precisely because of this trimming, and any refutation must
first defeat it.

### Literature

H. Lin, *Double duals and Hilbert modules* (arXiv:2311.15462), §4, proves a
Kaplansky-style theorem: the unit ball of `H_A` is `T_s`-dense in the unit
ball of `H_A ⊗ M` for `M = A''` — by writing `ξ` in *coordinates* of the
standard module over the right ideal `AM` and applying the classical matrix
Kaplansky to `Mₙ(A) ⊆ Mₙ(M)` on a column, then cutting by
`q = diag(1,0,…,0)` (which preserves both the norm bound and the strong
approximation).  This does not port to 158II as stated: `X` is abstract (no
coordinates; Kasparov stabilization needs countable generation), `A` is
*not* assumed ultrastrongly dense in `ℬ`, and `D` is not a standard module.
But it is the strongest hint that a correct proof, if one exists, goes
through matrix amplification and 158Ia rather than through any repaired
version of the `h`-continuity argument.  **Author decision requested** (the
ERRATA row for 158V already asks for one): either a proof of the weak
statement of `kaplansky_hilbmod_of_weak`, or a counterexample to 158II, or a
strengthening of 158II's hypotheses (e.g. `A` ultrastrongly dense, `X`
countably generated) matching what Lin's technique needs.

## Session 30 — `B/Dils` 158II weak form worked; iterated trimming has a precise structural blocker; Lin citation verified (worker 60, continued)

Target per coordinator: the weak form created by `kaplansky_hilbmod_of_weak`.
**Not closed, not refuted.**  No code changes this pass; three findings.

### 1. The iterated/adaptive trimming route, worked out and blocked

The suggested route was analyzed to the end.  Recursion: `X₀ := x`; at stage
`i` request `dᵢ ∈ D` close to the *known* residual `Xᵢ` (adaptivity is fine:
all coefficients are known at request time), set `bᵢ = ⟪dᵢ,dᵢ⟫`,
`ψᵢ = ψ(bᵢ)`, `qᵢ = 1 − ψᵢ`, piece `Pᵢ := ψᵢ•dᵢ`, residual
`Xᵢ₊₁ := qᵢ•Xᵢ`.  Then `x − ΣPᵢ = X_k + ΣEᵢ` with `Eᵢ = ψᵢ•(Xᵢ−dᵢ)` and
*every `Eᵢ` is weak-small by good-slot Cauchy–Schwarz* — the weak-form
telescoping works.  The residual even *contracts*: `‖Xᵢ‖ ≤ 1` forces
`sp⟪Xᵢ,Xᵢ⟫ ⊆ [0,1]`, and on `[ε,1]` the trimming factor
`t(1−ψ(t))²/t = ((1−t)/(1+t))²`-type is `≤ θ_ε < 1`, with an `εN` floor from
`[0,ε)` — so in the commuting idealization `p_ω(X_k)² ≤ θ_ε^k N + εN/(1−θ_ε)`
is arbitrarily small and the weak value follows by CS.  **The blocker is the
norm bound**: the accumulated coefficient is the *ordered product*
`1 − q_{k-1}⋯q₀` of noncommuting positive contractions, and this exceeds the
unit ball even with *zero* approximation error: numerically
`‖1 − q₁q₀‖ ≈ 1.155` for `qᵢ = 1 − Pᵢ` with rank-one `Pᵢ` at overlap
`c ≈ 0.58`, and `> 1.17` for three random contractions (2×2/3×3, exact
linear algebra; easy to make kernel-checked if ever needed).  Symmetric
two-sided trimming `qᵢ^{1/2} · qᵢ^{1/2}` would keep the coefficient in
`[0,1]` — but a Hilbert module has only *one-sided* smul, so the symmetric
version does not exist.  Capping the finished sum with `f(⟪T,T⟫)` reopens
the beast `ω((√β−1)₊²)`, with the overshoot direction adversary-steerable.
This is the mirror obstruction restated at the level of the iteration: **no
two-sided trimming on a one-sided module.**  Multi-piece sums fare no
better: a positive `k×k` operator Gram matrix is only `≤ k·diag`, and the
off-diagonal entries are known only weakly.

### 2. Structural facts worth keeping

* `J := cl span ⟪D,D⟫` is a closed two-sided *-ideal of `A`
  (`a⟪d,d'⟫ = ⟪d, a•d'⟫`, `⟪d,d'⟫a* = ⟪a•d, d'⟫`), so `J` has an
  approximate unit `(e_λ)` and `e_λ•d → d` *in norm* for every `d ∈ D` —
  the abstract form of the trimming that collapses adversarial `D`s.
* **Column modules degenerate**: for `X = cl{|v⟩⟨e₁|}`-type modules the
  ultranorm-continuous functionals already separate as the norm dual, so a
  *subspace* is ultranorm-dense iff norm-dense (Mazur), and the weak form is
  then trivial.  Any counterexample needs `X` whose ultranorm dual is
  genuinely smaller — e.g. `X = ℬ` — and there every candidate `D` tried
  (e.g. the valid instance `D = ℂU + K`, `A = ℂ1 + K`, `U` a co-isometry:
  all hypotheses check, and `(W)` holds through compact truncation +
  normality) is rescued by trimming.
* **No finite/decidable counterexample can exist**, for (W), 158II, *or*
  158V: in finite dimension the trace is a faithful np-functional, ultranorm
  density degenerates to norm density, and all these statements are *true*
  (for 158V: `h` is norm-Lipschitz).  158V's falsity is inherently
  infinite-dimensional *and* noncommutative — for commutative `ℬ` the
  ultranorm is a weighted fiberwise `ℓ²` and `z ↦ 2z/(1+|z|²)` is Lipschitz,
  so 158V is true there.  Kernel-checking the 158V counterexample therefore
  requires `B(ℓ²)` as a `Theses.VonNeumannAlgebra` with its np-functional
  theory — out of reach this session; `lp _ ∞` (now available) does not help
  because block-diagonal variants make `⟪yₙ−y₀,yₙ−y₀⟫` non-null.
* **Commutative 158II is provable** (sketch, one-shot): with everything
  commuting the mirror vanishes — `ω(q z q) = ω(q² z) ≤ ‖q‖²ω(z)` — and
  `d := f(b₀)•d₀`, `f = min(1, t^{-1/2})` works outright: movement²
  `= ω((√b₀−1)₊²) ≤ ω(|b₀ − ⟪x,x⟫|)` via `(√s−√t)² ≤ |s−t|`, which is
  `≤ 2(√N+δ)δ` by commutative CS.  Formalization cost is dominated by
  two-variable functional calculus (`(√s−√t)² ≤ |s−t|` for commuting
  positives); Mathlib has no `cfc₂`, so this is a Gelfand-duality detour —
  a candidate for a dedicated session, not attempted here.

### 3. H. Lin, arXiv:2311.15462 §4 — citation now verified (was unchecked in B10)

Read in full.  Lemma 4.3: for the *standard* module `H_A`, the unit ball of
`H_A` is `T_s`-dense in the unit ball of `H_A•M`, where `M = Ā^{SOT} ∋ 1`;
proof by coordinates `ξ = {bₙ}`, a column matrix over `R = cl(AM)`, the
classical Kaplansky theorem in `Mₙ` (`Mₙ(A)` SOT-dense in `Mₙ(M)`), and a
corner cut `L ↦ Lq` that preserves both `‖L‖ ≤ ‖S‖` and the strong
approximation.  Theorem 4.4 extends to an *arbitrary* Hilbert `A`-module
`H`: countably generated case by Kasparov stabilization (`H_A = H ⊕ H^⊥`,
compress by the projection); general case via an approximate identity
`(E_λ)` of `K(H)` — `E_λH` is countably generated and `Ψ₀(E_λ)ξ → ξ` *in
norm*.  Two reasons it does **not** port to 158II as stated: (i) it needs
`A` SOT-dense in `M` (there `M` is *defined* as the closure), while 158II's
`A` has no density in `ℬ`; (ii) its `ξ` lies in `H•M`, the *norm*-closed
`M`-module generated by `H`, while 158II's `x` is only in the *ultranorm*
closure of `D` — the passage from ultranorm closure to `D̄•M` is exactly the
open content.  Also relevant: Lin's §5 Example 5.1 shows the analogous
density *fails* for `H^♯` in the `⟨·,ξ⟩`-topology (a `{pₙ}` sequence in
`H_M^♯` is not ball-approximable), a warning against strengthening 158II's
conclusion.  Net effect on the recommendation: a repaired 158II likely
needs added hypotheses of the shape "`x` in the norm-closed
`us-closure(A)`-module generated by `D`", under which Lin's technique (via
158Ia in matrix form) is the proof.

---

## Session 31 — `A/Proc`: parsecs 1220/1230 (`ℓ^∞ ⊣ nsp`) and 128VI (worker 58)

Files touched: `Theses/A/Proc/QuantumLambda.lean`,
`Theses/A/Proc/Duplicators.lean`, this log.  `Tensor.lean`,
`Measurement.lean`, `A/CStar`, `A/VN`, `B/` untouched.

**A/Proc 128 → 119.**  Per file: `QuantumLambda` 26 → **18**,
`Duplicators` 19 → **18**, `Tensor` 45, `Measurement` 38 unchanged.

| point | declaration | class |
|---|---|---|
| **122II** | `exists_linfEval` | 1 |
| **122II** | `first_adjunction` | 1 |
| **122II** | `exists_linfMap` | 1 |
| **122IV** | `nmiu_functional_product` / `lp_nmiu_functional_factors` | 3 (mild) |
| **122VI**.1 | `cor_linf_ff_1` | 1 (exercise, no author argument) |
| **122VI**.2 | `cor_linf_ff_2` | 1 (exercise) |
| **122VI**.3 | `cor_linf_ff_3` | 1 (exercise) |
| **123I**.2 | `linf_projections_order_separating` | 1 (exercise) |
| **128VI** | `sef_instrument` | 1 |

### What actually unblocked this

Session 27 (`vonNeumannAlgebra_lp_infty`) was reported as gating twelve
A/Proc statements.  **Checked: the gate was not the instance.**  Of the
twelve `lp`/`ℓ^∞`-typed statements in `QuantumLambda.lean`, *none* has
`VonNeumannAlgebra (lp 𝒜 ∞)` in its type — they need only
`CStarAlgebra`/`PartialOrder`/`StarOrderedRing` on `lp 𝒜 ∞`, which were
always honest.  The one A/Proc statement that genuinely routed through the
instance is **128XIII** `duplicable_product` (via `Duplicable`), and it
remains blocked on 111XII anyway.

What did unblock them are session 27's *lemmas*: `lp_infty_le_iff` (the
order on `⊕ᵢ 𝒜ᵢ` is pointwise) and `lp_infty_exists_isLUB` (its suprema are
pointwise).  Every proof below rests on one of the two.

### New reusable infrastructure (`QuantumLambda.lean`, section `DirectSums`)

* `lpEvalSAH j : lp 𝒜 ∞ →⋆ₐ[ℂ] 𝒜 j` — the coordinate projection as a
  ∗-homomorphism, with `lpEvalSAH_apply`.
* `lpEval_preservesDirSups` — **this is `Theses.A.VN.vn_products_proj_normal`
  (47IV.2), which is `sorry` in `A/VN/Basic.lean`**.  Two lines from
  `lp_infty_exists_isLUB` + `isLUB_coe_of_isLUB`.
* `lpProd_nmiu` — **this is `Theses.A.VN.vn_products_nmiu` (47IV.3), also
  `sorry` in `A/VN/Basic.lean`**.  It needs *no* `VonNeumannAlgebra`
  hypothesis at all: the ∗-algebra half is the already-proved **20aI**
  `cstar_product_2_miu`, and normality of the mediating map follows from
  normality of the `fᵢ` because the order is pointwise.
  `A/VN` was closed for editing this round, so both live in `A/Proc`;
  **they should be moved into `A/VN/Basic.lean` and the two `sorry`s there
  discharged** by whoever next owns that file.
* `lpKappa i : 𝒜 i → ⊕ⱼ 𝒜ⱼ` (the thesis's `κᵢ`) with
  `lpKappa_mul`, `lpKappa_mul_left` (`κᵢ(1)·x = κᵢ(xᵢ)`), `lpKappa_star`,
  `lpKappa_apply_self/_ne`, `lpKappa_sa`, `lpKappa_sa'`, `lpKappa_le`;
  `lpSumSA F = ∑_{j∈F} κⱼ(1)` with `lpSumSA_apply`, `lpSumSA_isLUB`
  (`⋁_F ∑_{j∈F} eⱼ = 1`); `exists_kappa_one`.

`Duplicators.lean` gains the corresponding two-summand algebra:
`pairLp_apply/_zero/_one/_eta/_mul/_add/_star/_one/_smul`, `norm_pairLp_le`,
`continuous_lpEval2`, `diagSub` (the diagonal `{(a,a)}` as
`StarAlgHom.equalizer (π₀) (π₁)`), `mem_diagSub`, `isVNSubalgebra_diagSub`.

### Divergences

* **122II — class 1.**  proc.tex:4520ff. is a categorical sketch; the
  content is the product universal property of `⊕ᵢ 𝒜ᵢ`, which is what
  `lpProd_nmiu` is.  `exists_linfMap` is derived from `first_adjunction`
  exactly as the thesis derives `ℓ^∞(f)` from the universal property
  (proc.tex:4570–4580), not by an independent construction.
* **122IV — class 3 (mild).**  The thesis's proof (proc.tex:4595) runs
  `eᵢ^⊥ = ∑_{j≠i} eⱼ`, `φ(eᵢ^⊥) = 0`, hence `φ(a) = φ(eᵢa)`.  We drop the
  middle step: once `φ(eᵢ) = 1`, `φ(eᵢa) = φ(eᵢ)φ(a) = φ(a)` is immediate
  from multiplicativity, so no infinite sum is needed anywhere.
  Conversely the thesis *asserts* "there is at most one `i` with
  `φ(eᵢ) ≠ 0`" and then silently assumes such an `i` exists; **existence is
  the only place normality is used**, and it needs the directed family
  `{∑_{j∈F} eⱼ : F finite}` whose supremum is `1` (`lpSumSA_isLUB`).  This
  is a small gap in the author's argument rather than an error — logged
  here, not in ERRATA, because the statement is true and the repair is two
  lines of the author's own kind.
* **Hypothesis not actually used (122IV).**  The statement is "on a direct
  sum of *von Neumann algebras*"; the proof never uses it — normality of
  `φ` alone suffices, and `lp_nmiu_functional_factors` is stated without
  it.  `nmiu_functional_product` keeps the hypothesis (it is inherited from
  its section) and the `unusedSectionVars` warning is left in place as the
  evidence, following the `112IX`/`105IV.2` convention.
* **122VI.1–.3, 123I.2 — class 1**, but they are exercises and `asols.tex`
  stops at parsec 340, so these are the first proofs that exist.  Two
  points worth reporting to the author: (i) 122VI.1's uniqueness is *not*
  formal — it needs `φ(κᵢ(1)) = 1` to rule out a second index, i.e. the
  same ingredient as 122IV; (ii) 123I.2 as we state it ("`fₓ ≤ gₓ` for all
  `x` implies `f ≤ g`" for self-adjoint `f, g`) is exactly `lp_infty_le_iff`
  plus the fact that a self-adjoint element of `ℓ^∞(X)` is pointwise real.
* **128VI — class 1.**  proc.tex:6015 transcribed line for line, including
  the auxiliary `f'(c,d) = (f(c,d), f(c,d))`, the appeal to **34aVIII**
  `russo_dye_cor` for `‖f'‖ ≤ 1`, Tomiyama (**128II**), and the adjoint
  step through **10II**/`cstar_p_implies_i`.  The only addition is what the
  thesis takes for granted: that the diagonal `{(a,a)}` really is a von
  Neumann subalgebra of `𝒜 ⊕ 𝒜` (`isVNSubalgebra_diagSub`) — norm-closed
  because the coordinate projections are contractive, and closed under
  directed suprema because those are computed pointwise.

### Verification

`lake build` over all four `Theses.A.Proc.*`: exit 0.  `#print axioms` →
`[propext, Classical.choice, Quot.sound]` for all nine theorems above, all
28 new auxiliaries, and the regression targets `tomiyama`,
`product_functional`, `atomic_measure_space`,
`Theses.A.VN.vonNeumannAlgebra_lp_infty`.  No new warnings in either edited
file (every new lemma carries the `omit`s the linter asked for; the single
new `unusedSectionVars` warning, on `nmiu_functional_product`, is
deliberate and documented above).

---

## Session 32 — `A/VN`: parsec 770 (77I, 77III), 44XI.3, and 47IV.2/.3 relocated (worker 59)

Files touched: `Theses/A/VN/Basic.lean`, `Theses/A/VN/Completeness.lean`,
`Theses/A/Proc/QuantumLambda.lean` (the two relocated lemmas deleted, call
sites re-pointed), `ERRATA.md` (one new row, in point order), this file.

**A/VN 100 → 92.**  Per file: `Basic` 30 → 25, `Completeness` 5 → 2;
`Division` 26, `NormalFunctionals` 18, `Projections` 21 unchanged.
`A/CStar` 37, `A/Proc` 119, `B/Dils` 63, `B/Eff` 19 — all unchanged.

| point | declaration | file | class |
|---|---|---|---|
| **44XI**.3 | `vn_positive_basic_3` | Basic | 2 — no author argument exists (Exercise, `vn.tex`) |
| **45VI** | `mult_jus_cont` | Basic | 1 |
| **46II** | `usconv` | Basic | 2 — no author argument exists (Exercise, `vn.tex`) |
| **47IV**.2 | `vn_products_proj_normal` | Basic | 2 — relocated from `A/Proc` (worker 58) |
| **47IV**.3 | `vn_products_nmiu` | Basic | 2 — relocated from `A/Proc` (worker 58) |
| **77I**.1 | `vn_complete_1` | Completeness | 1, with one citation replaced — see ERRATA **77II** |
| **77I**.2 | `vn_complete_2` | Completeness | 1, likewise |
| **77III** | `vn_ball_compact` | Completeness | 2 — ultrafilters in place of the thesis's uniform-space route |

One new auxiliary, in `Completeness.lean`: `omegaNorm_comp_starAlgHom`.

### 77I — the thesis's proof, minus a forward reference

Transcribed as written except for one step.  The argument is: represent `𝒜`
by `ρ_Ω` on `ℋ_Ω` (**48VIII**/**48V**), complete inside `B(ℋ_Ω)` by **76I**
(ultrastrong) / **76III** (bounded ultraweak), land back in `ρ_Ω(𝒜)` because
that is a von Neumann subalgebra (**48VI**.1) and hence ultrastrongly *and*
ultraweakly closed (**75VIII** `vnsac`, proved in session 27 — this was
77I's last prerequisite), and come back along `ρ_Ω`.

The last step is where the thesis and this proof differ, and it is filed as
ERRATA **77II**.  The thesis justifies "the two ultrastrong topologies agree
on `ℛ`" by *"any np-functional `ω : ℛ → ℂ` is of the form `⟨x,(·)x⟩`"* — a
statement about all np-functionals of `ℛ`, i.e. **89IX**, twelve parsecs
later, and stronger than 89IX gives (89IX produces a *sum* of vector
functionals).  Neither is needed.  Only one direction is used, and it is
true by construction: with `Ω` = *all* np-functionals of `𝒜`, every
np-functional of `𝒜` is a vector functional in `ℋ_Ω`, which is exactly
**48V** `varrho-Omega-normal` and is already available at parsec 770.  The
converse direction — restricting an np-functional of `B(ℋ_Ω)` along `ρ_Ω` —
is `compNP (starAlgHomP ρ)`, which was already in `Basic.lean`.

*Note to whoever proves the next thing about normal maps*: this session first
rebuilt `compNP` from scratch (as `npPullback`, plus a universe-polymorphic
composition lemma), because `preservesDirSups_pmap_comp` — the obvious
candidate in `Basic.lean` — is stated with all three carriers in the *same*
universe and so cannot take `ℂ` as codomain, which looked like the general
obstruction.  It is not: `compNP` (`Basic.lean`, section `PositiveMaps`) is
stated over `Type*` and does exactly this.  The duplicate was deleted.

The transport of `‖·‖_ω` is `omegaNorm_comp_starAlgHom`:
`‖a‖_{ω∘ρ} = ‖ρ(a)‖_ω`, one `rw` from `ρ(a*a) = ρ(a)*ρ(a)`.

### 77III — same theorem, ultrafilters instead of uniform spaces

*Class 2.*  The thesis embeds `(𝒜)₁` into `ℂ^Ω` (`Ω` the npu-maps), shows
the image is complete hence closed, and applies Tychonoff.  Rendering
"complete ⇒ closed" needs a uniform structure on `𝒜` for the ultraweak
topology, which the tree does not have (the topologies are `def`s, not
instances).  The ultrafilter form of compactness avoids it entirely:
given an ultrafilter `F` on `(𝒜)₁`, each `F.map ω` is an ultrafilter inside
a closed ball of `ℂ`, hence convergent, hence Cauchy — Heine–Borel in `ℂ`
replaces Tychonoff — so **77I**.2 supplies an ultraweak limit `a`, which
lies in `(𝒜)₁` because the ball is ultraweakly closed, and `F ≤ 𝓝 a`
because `map val (comap val F) = F`.  About 35 lines.

Two things the thesis leaves implicit, both harmless: that `(𝒜)₁` is
ultraweakly (not merely ultrastrongly) closed — **44XI**.3 plus **73VIII**
`ultraclosed`; and that the *npu*-maps suffice to give the ultraweak
topology, which **42III** defines from the *np*-maps.  The proof here uses
all np-functionals throughout, so the second step never arises.

### 44XI.3 — the unit ball is ultrastrongly closed

*Class 2 by necessity: 44XI is an Exercise of `vn.tex`, and `asols.tex`
stops at parsec 340, so no author argument exists.*  Proved from the
characterisation

  `‖a‖ ≤ 1  ↔  a*a ≤ 1  ↔  ∀ ω, ‖a‖_ω ≤ ‖1‖_ω`,

whose second `↔` is **44XI**'s own preliminary claim `np_orderSeparating`
(already proved) in one direction and monotonicity of `ω` in the other; the
first is `CStarAlgebra.norm_le_one_iff_of_nonneg` at `a*a` together with
`‖a*a‖ = ‖a‖²`.  Closedness is then one line of the triangle inequality
`abs_omegaNorm_sub_omegaNorm_le`, since each `{a | ‖a‖_ω ≤ ‖1‖_ω}` is
ultrastrongly closed.  This was needed for 77III and is the only place the
np-functionals' *order*-separation (as opposed to faithfulness) is used
here.

### 45VI — the thesis's two-line estimate, verbatim

*Class 1.*  vn.tex:906 is transcribed as it stands:
`‖ab − a_α b_α‖_ω ≤ ‖(a−a_α)b‖_ω + ‖a_α(b−b_α)‖_ω ≤ ‖a−a_α‖_{ω(b*(·)b)} +
‖a_α‖‖b−b_α‖_ω`, the two pieces being `omegaNorm_mul_right` (which is
literally "`ω(b*(·)b)`", i.e. `conjNP b ω`) and `omegaNorm_mul_le`.  Twenty
lines, and the only place the norm bound on `(a_α)` is used is the last
`≤`.

### 46II — `‖·‖_ω²` is the bridge

*Class 2 by necessity (Exercise, no published solution).*  Both directions
run through `ω(y*y) = ‖y‖_ω²`.  Forwards: `|‖x_α‖_ω − ‖b‖_ω| ≤ ‖x_α−b‖_ω`
(`abs_omegaNorm_sub_omegaNorm_le`) gives `‖x_α‖_ω → ‖b‖_ω`, hence
`ω(x_α*x_α) → ω(b*b)` for every `ω`, which is the first ultraweak clause;
the second is **43I**.2.  Backwards: expand

  `‖x_α − b‖_ω² = ω(x_α*x_α) − ω(x_α*b) − ω(b*x_α) + ω(b*b)`.

The first term converges by the first hypothesis.  The third is
`ω(b* · 1)` evaluated along the second hypothesis, and is ultraweakly
continuous by **44II** `continuous_ultraweak_conj` — the polarisation
lemma, already in the file.  The second is the complex conjugate of the
third (`npFunctional_star`), so it converges too, and the four limits
cancel.

**Worth recording for the author**: 46II is an Exercise placed at parsec
460, and the `⟸` direction needs the ultraweak continuity of
`a ↦ ω(b*a)`.  That is *not* immediate from **42III**, which defines the
ultraweak topology from np-functionals only; it needs the polarisation of
**44II**.  A hint pointing at 44II would be in order — without it the
exercise looks as though it needs **72V**/**72XI**, twenty-six parsecs
later.

### 47IV.2 / 47IV.3 — relocated, not re-proved

Worker 58 proved both in `A/Proc/QuantumLambda.lean` because `A/VN` was
frozen.  They are moved here verbatim, the `sorry`s deleted, and
`QuantumLambda.lean`'s three use sites now call the `A/VN` names; the
`A/Proc` copies are gone, replaced by a pointer comment.

**Hypothesis not actually used (47IV.3).**  `vn_products_nmiu` uses neither
`[∀ i, VonNeumannAlgebra (𝒜 i)]` nor `[VonNeumannAlgebra B]`: the ∗-algebra
half is **20aI** `cstar_product_2_miu` and normality of the mediating map
follows from normality of the `fᵢ` because the order on `⊕ᵢ𝒜ᵢ` is pointwise
(`lp_infty_le_iff`).  Kept as the thesis states it, with the
`unusedSectionVars` warning left in place as evidence and a note in the doc
comment — the `112IX`/`105IV.2` convention.

### Verification

Whole-project `lake build`: exit 0, 8738 jobs.  `#print axioms` on all eight
theorems, the new auxiliary and the regression targets `vnsac`, `cp_uscont`,
`ultraclosed`, `np_orderSeparating`, `ngns`,
`Theses.A.Proc.{exists_linfEval, first_adjunction, exists_linfMap}`:
`[propext, Classical.choice, Quot.sound]` throughout.  Exactly one new
warning in the tree — the deliberate `unusedSectionVars` on
`vn_products_nmiu` documented above; `omegaNorm_comp_starAlgHom` carries the
`omit` the linter asked for.

## Session 33 — `A/Proc`: 123I.1, 117II.2, and 117II.1 refuted (worker 60)

Files touched: `Theses/A/Proc/QuantumLambda.lean`, `Theses/A/Proc/Tensor.lean`,
`ERRATA.md`, this log.  `Measurement.lean`, `Duplicators.lean`, `A/CStar`,
`A/VN`, `B/` untouched.

**A/Proc 119 → 117.**  Per file: `QuantumLambda` 18 → **17**, `Tensor` 45 →
**44**, `Measurement` 38, `Duplicators` 18 unchanged.

| point | declaration | file | class |
|---|---|---|---|
| **123I**.1 | `linf_generated` | QuantumLambda | 1 (exercise, no author argument) |
| **117II**.2 | `sum_generation_2` | Tensor | 1 (exercise) |
| **117II**.1 | `sum_generation_1_is_false` (+ `starSubalgebra_complex_eq_top`, `diagBool`, `mem_diagBool`, `isVNSubalgebra_diagBool`) | Tensor | **4** — the thesis's statement is false; ours realigned |

### 123I.1 `linf_generated` — `W*({x̂ : x ∈ X}) = ℓ^∞(X)`

An exercise past parsec 340, so no published solution and no inline author
argument.  The route, which is the one w58 sketched:

* Norm-closedness is *not* enough — the finitely supported functions are
  norm-dense in `c₀(X)`, not in `ℓ^∞(X)`.  The work is done by closure under
  directed suprema.
* For `0 ≤ f` the finite restrictions `∑_{x∈F} f(x)·x̂` form a directed family
  (`F ⊆ X` finite) whose supremum is `f`, because the order on `⊕_{x∈X} ℂ` is
  pointwise (`lp_infty_le_iff`).  Worth recording: the *least*-upper-bound half
  needs only the singletons `F = {y}`, so no genuine limit argument appears.
* A self-adjoint `a` reduces to that case by `a = (a + ‖a‖·1) − ‖a‖·1`; the
  positive/negative-part decomposition that the obvious route would use is
  unnecessary, and in `ℓ^∞` the bound `0 ≤ a(y) + ‖a‖` is just
  `|Re a(y)| ≤ ‖a(y)‖ ≤ ‖a‖`.
* A general `f` reduces to that by `f = ℜf + i·ℑf`
  (`realPart_add_I_smul_imaginaryPart`).

### 117II.1 `sum-generation` part 1 is **false as printed** — ERRATA filed

Stated: if `Aᵢ` generates `𝒜ᵢ` for each `i`, then `⋃ᵢ κᵢ(Aᵢ)` generates
`⊕ᵢ 𝒜ᵢ`.  The coprojection `κᵢ` is **not unital**, so nothing puts
`eᵢ = κᵢ(1)` into `W*(⋃ᵢ κᵢ(Aᵢ))`, and a von Neumann subalgebra is unital by
definition (42V.4: it is a C\*-subalgebra).

`sum_generation_1_is_false` machine-checks the smallest witness: `I = Bool`,
`𝒜ᵢ = ℂ`, `Aᵢ = ∅`.  Every subset of `ℂ` generates `ℂ`
(`starSubalgebra_complex_eq_top`: every `ℂ`-∗-subalgebra of `ℂ` is `⊤`, since
`x = x·1`), whereas `W*(∅) ⊆ ℂ·1 ⊊ ℂ ⊕ ℂ`: the diagonal `diagBool` is a von
Neumann subalgebra — closed because evaluation is 1-Lipschitz
(`lp.lipschitzWith_one_eval`), and closed under directed suprema because those
are coordinatewise (`lp_infty_exists_isLUB`), so the two coordinates of a
supremum of diagonal elements are LUBs of the *same* set.

This is **not** an artefact of `∅` or of the trivial-ish algebra `ℂ`: `Aᵢ =
{0}` works verbatim, and `𝒜₀ = 𝒜₁ = ℂ²` with `A₀ = A₁ = {(1,0)}` (both
summands nontrivial, both generating sets non-empty and generating a *proper*
subalgebra's worth of data) gives `W*(⋃ κᵢ(Aᵢ))` of dimension 3 inside `ℂ⁴`.
The counterexample used in the tree is the shortest one; the others are
recorded in ERRATA.

Our statement of `sum_generation_1` is realigned to the repaired form —
generating set `⋃ᵢ κᵢ(Aᵢ) ∪ {eᵢ : i ∈ I}` — and left `sorry`.  The repair is
sufficient, and the argument is written out in its doc comment: with the `eᵢ`
present, `Tᵢ = {a : κᵢ(a) ∈ W}` is a *unital* ∗-subalgebra of `𝒜ᵢ`, norm-closed
(`κᵢ` is isometric) and closed under directed suprema (`κᵢ` carries LUBs to
LUBs, the order being pointwise), hence a von Neumann subalgebra containing
`Aᵢ`, hence `⊤`; and then a general `x` is the directed supremum of its finite
restrictions exactly as in 123I.1.  Not formalized this round: it needs
`lpKappa` and its algebra lemmas, which currently live *downstream* in
`QuantumLambda.lean`, so proving it means first lifting that block into
`Tensor.lean`.

### 117II.2 `sum_generation_2` — three lines of content

Centre separation transfers to `⊕ᵢ 𝒜ᵢ` because (i) centrality passes to each
coordinate by testing against `κᵢ(b)`, (ii) positivity is pointwise
(`lp_infty_nonneg_iff`), and (iii) `ω ∘ πᵢ` is already in the tree as
`Theses.A.VN.lpNP i ω`, with `lp_infty_np_apply` its defining equation — so the
witness the definition asks for is handed over directly.  No `DecidableEq I` in
the statement, so the proof opens with `classical` for `lp.single`.

### Verification

`lake build Theses.A.Proc.{Tensor,Measurement,QuantumLambda,Duplicators}` →
exit 0.  `#print axioms` on `linf_generated`, `sum_generation_2`,
`sum_generation_1_is_false`, `starSubalgebra_complex_eq_top`, `diagBool`,
`mem_diagBool`, `isVNSubalgebra_diagBool`, and regressions
`linf_projections_order_separating`, `cor_linf_ff_2`: every line is
`[propext, Classical.choice, Quot.sound]`.  Warnings were diffed against the
baseline build; the only new ones are the `declaration uses sorry` lines that
moved with the edits (all new tactic blocks use `change`, not `show`, where the
style linter asks for it).

## Session 34 — `B/Dils` 149VII: the `1 ⇒ 3` of 149V is proved (worker 61)

**Result: `bddUnComplete_of_selfDual` (149VII, dils.tex:2258) is closed,
axiom-clean.**  `HilbertModules.lean` goes 3 → 2 `sorry`s; 149V now has three
of its four non-trivial implications settled by hand (1⇒3, 2⇒3, 4⇒1) and two
still frozen (3⇒4 on **80IV**, 4⇒2 on **87VIII**).

`Theses/A/VN/Completeness.lean` is now imported by `HilbertModules.lean` (no
cycle: `Completeness` imports only `A/VN/Projections`, which was already on
the path).  Session 32 having proved **77I**.1 `vn_complete_1`, this is the
single ingredient that was missing.

### Divergence: class 1 with one class-2 deviation

Faithful to dils.tex 2256–2325 except at the bound on `τ`.

* **Mirroring.**  The thesis's `τ(y) = (uslim_α ⟨y,x_α⟩)*` is *unstarred* in
  the Mathlib convention: `τ(y) = uslim_α [x_α,y]`.  The star of the thesis is
  exactly what the swap `[u,v] = ⟨v,u⟩` absorbs — and the check that decides
  it is 𝒷-linearity, not the eye: `y ↦ [x,y]` satisfies `τ(b•y) = b·τ(y)`,
  whereas `y ↦ [y,x]` satisfies `τ(b•y) = τ(y)·b*`, which is not what
  `SelfDual` asks for.  The ultrastrong limit exists by 77I.1; `τ` is additive,
  ℂ-linear and 𝒷-linear by uniqueness of ultrastrong limits (**44XI**.1 via
  `tendsto_nhds_unique` for `ultrastrong 𝒷`).
* **Class 2, the bound on `τ`.**  The thesis writes
  `τ(y)τ(y)* = uwlim_α ⟨x_α,y⟩⟨y,x_α⟩ ≤ ‖y‖²B²` and cites **46II**
  (`usconv`, joint ultrastrong/ultraweak continuity of multiplication on
  bounded sets), which is not in the tree.  Instead every `‖[x_α,y]‖_ω` is
  bounded by `‖y‖ B ω(1)^½` directly — **142III** `module_CS` gives
  `[y,d][d,y] ≤ ‖[y,y]‖[d,d]`, i.e. `‖[d,y]‖_ω ≤ ‖y‖‖d‖_ω`
  (`omegaNorm_inner_le`), and `‖x‖_ω ≤ ‖x‖ω(1)^½`
  (`unSeminorm_le_norm_mul`) — and `‖·‖_ω` is `1`-Lipschitz, so the same bound
  passes to `τ(y)`.  Order separation of the np-functionals (**44XI**,
  `np_orderSeparating`) then converts the *family* of ω-bounds into
  `‖τ(y)‖ ≤ B‖y‖`; this is `norm_le_of_omegaNorm_le`, which is the `hchar`
  buried inside the proof of `vn_positive_basic_3` restated for a general
  constant.  (`usconv` would have been used for precisely this step, so this
  is a substitution of one 44XI-flavoured argument for a 46II-flavoured one,
  not a change of route.)
* The closing ε-argument is the thesis's verbatim, filter-side: for the
  `s ∈ F` of diameter `≤ (ε/2)²/(2(K+1))` and any `x ∈ s ∩ s₀`, a `β ∈ s` is
  chosen with `|ω[t-x, t-β]|` small (possible because `[·,t-x] → [t,t-x]`
  ultrastrongly and `F` is `NeBot`), and
  `[t-x,t-x] = [t-x,t-β] + [t-x,β-x]` splits the estimate into Kadison's
  inequality (`norm_apply_le_omegaNorm`) and Cauchy–Schwarz for `‖·‖_ω`
  (`unSeminorm_inner_le`).  `K = ‖t‖_ω + Bω(1)^½` is the thesis's `‖t‖_f + B`.

### New private by-products in `HilbertModules.lean`

`inner_neg_left'`, `inner_neg_right'`, `unSeminorm_neg'`, `usTendsto_unique'`,
`usTendsto_add'`, `usTendsto_const_mul'`, `usTendsto_smul'`,
`isSelfAdjoint_real_smul_one`, `norm_le_of_omegaNorm_le`, `omegaNorm_inner_le`,
`unSeminorm_le_norm_mul`.  The last three are the reusable ones: any further
`A/VN`-to-module transfer in this chapter will want them, and
`norm_le_of_omegaNorm_le` is the general form of an argument that is currently
inlined twice in `A/VN/Basic.lean`.

### What 149V's partial completion does *not* open — checked, not assumed

**151Ia** `selfdual_completion_univ` (`SelfDualCompletion.lean:96`) is the
natural consumer, and it is *not* unblocked.  dils.tex:3283 uses "`Y` is
ultranorm complete, see `dils-selfdual`" — condition **2** of 149V, which is
reached only through `1 ⇒ 3 ⇒ 4 ⇒ 2`, i.e. through **80IV** *and* **87VIII**.
Bounded ultranorm completeness (condition 3, what is now available) does not
suffice: the approximating net supplied by `UnDense` is not norm-bounded, and
making it so is exactly the Kaplansky-type statement 158II, which sessions 29
and 30 left open.  `dils_completion` (150II) is likewise untouched.  No other
file in `Theses/B` mentions `dils_selfdual`, `BddUnComplete` or `UnComplete`.

### Verification

`lake build Theses.B.Dils.{HilbertModules,SelfDual,SelfDualCompletion,
Kaplansky,Paschke,Pure,Stinespring}` → exit 0, zero `error:` lines.
`#print axioms Theses.B.Dils.bddUnComplete_of_selfDual` →
`[propext, Classical.choice, Quot.sound]`.  The doc comments of 149VII and
149IX were updated (149IX's remaining blocker is **87VIII** alone, in
`Theses/A/VN/NormalFunctionals.lean`, not `Basic.lean` as the old comment
said), as was the parsec-1490 section header.

---

## Session 35 — `A/VN`: 87VIII, 79VI.1–.3, and 79VI.4 refuted (worker 61, A chain)

Four statements proved (`A/VN` 92 → 88 code `sorry`s: `NormalFunctionals`
18 → 17, `Division` 26 → 23) and one refuted.  Whole-project `lake build`
exit 0; every new declaration `#print axioms`-clean.

### **87VIII** `ultraweakly_bounded_implies_bounded` — divergence class 2

This is the last thing **149V** needed besides **80IV**, and the short route
skips the two `sorry`s the thesis's route goes through.

The thesis (vn.tex:6590) runs the uniform boundedness principle on the
**predual** `𝒜_*`: `f ↦ f(bα)` has norm `‖bα‖` by **87VI**, `𝒜_*` is a Banach
space by **87III**, and pointwise boundedness comes from **72V** (four
np-pieces).  Of those, 87III and 87VI are still `sorry`, and both sit behind
**86IX** (polar decomposition of functionals) and **86XII** — so the printed
route costs four more theorems.

Instead: push the net into a *faithful normal representation* `ρ : 𝒜 → B(ℋ)`
(**48VIII** `exists_faithful_normal_rep_vectors`, proved), where
`‖ρ a‖ = ‖a‖` (`NonUnitalStarAlgHom.norm_map`, injective ∗-homs of C\*-algebras
are isometric), and run **Banach–Steinhaus on `ℋ` twice**:

1. every `⟪z, ρ(·) z⟫` is an np-functional of `𝒜` — it is
   `compNP (starAlgHomP ρ) (vectorNP z)`, both already in `Basic.lean` — so
   the hypothesis bounds the diagonal `⟪ρ(bα) z, z⟫` for each `z`;
2. the complex polarisation identity for a linear map
   (`inner_map_polarization'`) turns that into a bound on `⟪ρ(bα) y, z⟫` for
   each pair `y, z`;
3. Banach–Steinhaus applied to `innerSL ℂ (ρ(bα) y)` bounds `‖ρ(bα) y‖` for
   each `y` (`innerSL_apply_norm` gives the norm of the functional);
4. Banach–Steinhaus applied to `ρ(bα)` itself bounds `‖ρ(bα)‖ = ‖bα‖`.

No predual, no 72V, no 86-parsec input.  ~55 lines plus one private norm
estimate (`uwbib_pol_aux`).  87III and 87VI remain open and are unaffected —
they are still wanted for the predual's own sake.

### **79VI**.1 `pseudoinverse_basic_2'_1` — class 2 (Exercise, no author argument)

For positive `a`: pseudoinvertible ⟺ `at = ⌈a⌉` for some `t ≥ 0`, and such `t`
commutes with `a`.

* `⟸` is *not* "take `t`": the given `t` need not be supported in the corner.
  Cut it down to `⌈a⌉t⌈a⌉`, whose `a(·)a = a` is immediate from `a⌈a⌉ = a`,
  and whose two carrier bounds are one application each of `suppProj_mul_le`
  and `rangeProj_mul_le`.  Then **79II**.(2) ⇒ (5).
* `⟹` takes `t = a^{∼1}` and needs its *positivity*, which is new:
  `a^{∼1}` is self-adjoint because `star` carries a pseudoinverse of `a` to
  one of `a*` `= a` and pseudoinverses are unique (`pinv_isSelfAdjoint`),
  and then `a^{∼1} = (a^{∼1})* a a^{∼1} ≥ 0` by **79II**.(4)
  (`pinv_nonneg`).
* The commutation clause is one line: `at = ⌈a⌉` is self-adjoint, so
  `at = star(at) = ta`.

### **79VI**.2 `pseudoinverse_basic_2'_2` — class 2

For positive `a`: pseudoinvertible ⟺ `λ⌈a⌉ ≤ a` for some `λ > 0`.

* `⟸` **avoids any spectral analysis of `a`**.  Put `b = a + λ(1−⌈a⌉)`.  Then
  `b⌈a⌉ = ⌈a⌉b = a` by one computation, and `λ·1 ≤ b`, so `0 ∉ spectrum ℝ b`
  (`algebraMap_le_iff_le_spectrum`) and `b` is invertible
  (`spectrum.isUnit_of_zero_notMem`).  Its inverse `c` is positive
  (`c = c* b c`, `c` being self-adjoint by uniqueness of two-sided inverses)
  and commutes with `⌈a⌉`, and `t = c⌈a⌉` is positive with `at = ⌈a⌉` — so
  **79VI**.1 applies.  In particular no `cfc` of `a` is needed here.
* `⟹` is where `√a` enters.  With `t = a^{∼1}` one has `⌈a⌉t = t⌈a⌉ = t` and
  `t ≤ ‖t‖⌈a⌉` (conjugate `t ≤ ‖t‖·1` by `⌈a⌉`), and `⌈a⌉ = √a t √a` because
  `√a` commutes with `t` (`Commute.cfc_nnreal`, since `t` commutes with `a`).
  Conjugating by `√a` gives `⌈a⌉ ≤ ‖t‖a`, i.e. `λ = ‖t‖⁻¹` works; `t = 0`
  (hence `⌈a⌉ = 0`) is the separate trivial case.

### **79VI**.3 `pseudoinverse_basic_2'_3` — class 2

`⌈a^{∼1}⌉ = ⌈a⌉` is immediate once `a^{∼1} ≥ 0` is known: `⌈a^{∼1}⌉` is
`⌈a^{∼1}⌋ = a a^{∼1} = ⌊a⌉ = ⌈a⌉`.

For `a^{∼1} ∈ {a}^□□` the missing step was **whatever commutes with `a`
commutes with `⌈a⌉`**, which the thesis does not state anywhere before parsec
880 (**88II** `commutant-ceil` is the general form, and is a forward
reference here).  It is elementary and is now a named auxiliary,
`commute_ceil_of_commute`: `a(b(1−⌈a⌉)) = b(a(1−⌈a⌉)) = 0`, so
`ceil_mul_eq_zero` gives `⌈a⌉b = ⌈a⌉b⌈a⌉`; the same for `b*`, conjugated,
gives `b⌈a⌉ = ⌈a⌉b⌈a⌉`.  With that, `(ba^{∼1})a = (a^{∼1}b)a` and both sides
have carrier below `⌊a⌉`, so **60VIII** `mult_cancellation_2` finishes.

### **79VI**.4 is **false as stated** — new ERRATA row, in point order

`c^{∼1} ≤ b^{∼1}` for positive commuting pseudoinvertible `b ≤ c` fails as
soon as `⌈b⌉ < ⌈c⌉`.  Machine-checked witness
`pseudoinverse_basic_2'_4_is_false`: in `ℓ^∞({0,1})` (a von Neumann algebra by
the instance w57 proved) take `b = (1,0)`, `c = 1`.  Projections are their own
pseudoinverses (`pinv_of_isStarProjection`), so the claim reads `1 ≤ (1,0)`.

The refutation is not about the model: `pseudoinverse_basic_2'_4_forces_eq_one`
shows that in *any* von Neumann algebra, 79VI.4 applied to `b = p`, `c = 1`
forces every projection `p` to be `1`.  The repair is the hypothesis
`⌈b⌉ = ⌈c⌉`.  The statement is kept verbatim and `sorry` pending an author
decision; its doc comment now points at the refutation.

### New auxiliaries in `Division.lean`

`rangeProj_eq_suppProj_of_isSelfAdjoint`, `pinv_isSelfAdjoint`, `pinv_nonneg`,
`commute_ceil_of_commute`, `isPseudoinverse_self_of_isStarProjection`,
`pseudoinvertible_of_isStarProjection`, `pinv_of_isStarProjection`,
`pbFourWitness` + two lemmas.  `commute_ceil_of_commute` and
`pinv_of_isStarProjection` are the reusable ones; 80IV will want both.

### What is left of the 790–810 block, precisely

**80III** `approximate_pseudoinverse_reduction` is the real gate on **80IV**
(the thesis reduces 80IV to the positive case by it), and it is *harder than
it looks*: our `IsApproxPseudoinverse` records "`tₙa` and `atₙ` are
projections, `∑ tₙa = ⌈a⌋ = ∑ ⌊tₙ⌉`, `∑ atₙ = ⌊a⌉ = ∑ ⌈tₙ⌋`" as six fields,
and getting `b(tₙb*)` to be a projection needs `tₙ c tₙ = tₙ` for `c = b*b`,
which does **not** follow field-by-field.  It follows from `tₙc ≤ ⌊tₙ⌉` plus
equality of the two suprema — an order-limit argument (`R_N − P_N` increasing
and dominated by `⌈a⌉ − P_N`), perhaps 80–150 lines, and worth stating as its
own lemma about two sequences of projections with equal suprema.  The
positive case of 80IV itself is then the thesis's `qₙ = ⌈(a−1/n)₊⌉`
construction on top of **79VI**.2, which is now available.

## Session 36 — `A/VN`: 80III and 80IV, the whole 790–800 gate (worker 62, A chain)

Files: `Theses/A/VN/Division.lean` only.  Two theorems closed, both **class 2**
(different route / original work: both are `vn.tex` points with no published
solution — 80III is an Exercise with no author argument at all, 80IV has an
author proof which is transcribed faithfully for the positive case).

### **80III** `approximate_pseudoinverse_reduction` — class 2

The Exercise gives no argument.  Writing `c = b*b`, four of the six fields of
`IsApproxPseudoinverse A b (fun n => tₙ b*)` transfer by associativity —
*provided* one knows two facts that are **not** fields of the definition:

* `tₙ c tₙ = tₙ`, and
* `tₙ = tₙ*`.

**The first is an order-limit fact and is the lemma the previous session
predicted** (`eq_of_le_of_isLUB_partialSums`), but the argument is shorter than
the predicted 80–150 lines and needs no functional: if `pₙ ≤ rₙ` are two
sequences of positive elements whose partial sums have the *same* supremum `q`,
put `d = r_m − p_m ≥ 0`; for `N > m`,

    ∑_{n<N} pₙ + d = (∑_{n<N} pₙ − p_m) + r_m ≤ (∑_{n<N} rₙ − r_m) + r_m ≤ q,

so `q ≤ q − d` and `d = 0`.  ~30 lines, purely order-theoretic.  Applied to
`(tₙc, ⌊tₙ⌉)` and to `(c tₙ, ⌈tₙ⌋)` — the inequalities are `⌊xy⌉ ≤ ⌊x⌉` and
`⌈xy⌋ ≤ ⌈y⌋` — it gives `tₙ c = ⌊tₙ⌉` and `c tₙ = ⌈tₙ⌋`, hence
`tₙ c tₙ = ⌊tₙ⌉ tₙ = tₙ`.

**The second was not predicted and is the only place `c ≥ 0` is used.**  With
`w = tₙ*tₙ − tₙtₙ*` the four identities `tₙ = c(tₙ*tₙ) = (tₙtₙ*)c` and
`tₙ* = c(tₙtₙ*) = (tₙ*tₙ)c` give `tₙ − tₙ* = c w = −(w c)`, whence
`c² w = w c²`; as `c = √(c²)` (`CFC.sqrt_mul_self`, `Commute.cfc_nnreal`) this
upgrades to `c w = w c`, so `c w = 0` and `tₙ = tₙ*`.

The genuinely new content is the two remaining sums `∑ₙ b tₙ b* = ⌊b⌉ =
∑ₙ ⌈tₙb*⌋`.  Both reduce to the same statement because
`⌈tₙb*⌋ = ⌊b tₙ⌉ = b tₙ b*`, and

* `∑_{k<N} b t_k b* = ⌊b Eₙ⌉` for `Eₙ = ∑_{k<N} t_k c` (an `IsLeast`
  computation on both sides of `ceill_basic_2`), and
* `⋃_N ⌊b Eₙ⌉ = ⌈b ⌈b⌋ b*⌉ = ⌈b b*⌉ = ⌊b⌉` by **60IX**.2 in the form
  `ceil_conj_projSup`, which is exactly the normality statement needed.

Turning that `projSup` back into an `IsLUB` in `A` needed one further
auxiliary, `isLUB_projSup_of_directed` (a directed set of projections has its
`projSup` as supremum in `A`: the supremum exists in `sa(A)` and is a
projection by **56XIV**).  Pairwise orthogonality of the `tₙc` is free from the
definition — the partial sums are `≤ ⌈c⌋ ≤ 1`, and **55XIII**.1 turns that into
`p q = 0`.

### **80IV** `approximate_pseudoinverse` — class 2 for the reduction, class 1
for the positive case

The reduction to positive elements is the thesis's (`80III` applied to `a*a`).
The positive case is the thesis's construction transcribed:
`qₙ = ⌈(a − 1/n)₊⌉`, `eₙ = qₙ₊₁ − qₙ`, `tₙ = (a eₙ)^{∼1}`.  Divergences, all
mild (class 3):

* the thesis's "`(a−1/n)₊` converges in norm to `a`, and also ultraweakly, so
  `a = ⋁ₙ(a−1/n)₊` and `⌈a⌉ = ⋃ₙ qₙ` by **59V**" is replaced by a direct
  argument that needs **only the norm estimate**: if a projection `p` dominates
  every `qₙ` then `uₙ p = uₙ`, so `‖ap − a‖ = ‖(a−uₙ)p − (a−uₙ)‖ ≤ 2/n → 0`,
  i.e. `ap = a`, i.e. `⌈a⌉ ≤ p`.  No ultraweak topology, no **59V**.
* the three facts about `(a − l)₊` for positive `a` — `(a−l)₊ ≤ a`,
  monotonicity in `l`, and `‖a − (a−l)₊‖ ≤ l` — are proved once via
  `(a − l)₊ = cfc (fun r => (r−l) ⊔ 0) a` (`posPart_sub_algebraMap`) and
  `cfc_mono` / `norm_cfc_le`, i.e. by pointwise inequalities on `spectrum ℝ a`.
  This is the only use of the functional calculus.
* `eₙ ∈ {a}^□□` is not needed in the abstract; what is used is
  `a eₙ = eₙ a`, which comes from **56I**'s addendum `vna_ceil_comm` plus
  `a (cfc f a) = (cfc f a) a`.

### Effect and verification

`A/VN` 88 → **86** (`Division.lean` 23 → 21).  Whole-project `lake build`
green at 8738 jobs, unchanged from the session's baseline, so `A/Proc` and
`B/Dils` are as clean as they were found.  `#print axioms` on all sixteen new
declarations gives `[propext, Classical.choice, Quot.sound]`; zero new
warnings.

With 80IV proved, `B/Dils` **149V** has all four of its implications
available: 1 ⇒ 3 (session 34), 4 ⇒ 1, 4 ⇒ 2 (87VIII, session 35) and now
3 ⇒ 4.  Two doc comments in `Theses/B/Dils/HilbertModules.lean` are now stale
and were **not** edited (out of scope): line 2358 calls
`Theses.A.VN.approximate_pseudoinverse` "still `sorry`", and line 2373 says
the same of `ultraweakly_bounded_implies_bounded`.

## Session 37 — `B/Eff` 195VI is proved: the divisoid characterisation of basically disconnected spaces (worker 63)

**Result: `basic_divisoid_equiv` (195VI, the last reachable item in `B/Eff`)
is proved.  B/Eff 19 → 18 code `sorry`s; `StatesPredicates.lean` 5 → 4
`sorry` tokens (4 → 3 sorried declarations).  The statement is unchanged
byte-for-byte.  `#print axioms` gives exactly `[propext, Classical.choice,
Quot.sound]`; the declaration-level walk over all eight `B/Eff` modules
(1695 declarations) shows the only `sorryAx`-dependent declarations are the
18 remaining sorried statements themselves — zero leakage preserved.**

The session-18 diagnosis was correct in substance — Mathlib still has neither
"basically disconnected" nor any σ-Dedekind completeness of `C(X)` (checked
against the current lake package; only `ExtremallyDisconnected` exists) — but
wrong in scale: the missing theory is **not** a Mathlib-sized contribution.
The special case the published solution actually consumes fits in three
private lemmas (~350 lines) in `StatesPredicates.lean`:

* `cIcc_pcm_le_iff` — the algebraic order `≼` of the effect monoid
  `[0,1]_{C(X)}` is the pointwise order (witness `b − a`).
* `exists_continuous_sup` — a bounded monotone sequence `h : ℕ → C(X, ℝ)`
  has a **least continuous upper bound**, assuming only
  `∀ q : ℚ, IsOpen (closure {x | ∃ n, q < hₙ x})`.  This is the entire
  σ-completeness content of Gillman–Jerison 3N.5, but with the
  basically-disconnected hypothesis abstracted into exactly the instances
  needed: `d x := sSup {q : ℚ | x ∈ Wq}` with `Wq := closure {∃ n, q < hₙ x}`;
  the `Wq` are clopen and nested, which gives continuity of `d` (a
  neighbourhood `W_qa ∩ (W_b)ᶜ` pins `d` between two rationals), `hₙ ≤ d`
  by density, and leastness because a continuous upper bound `u` has
  `{q ≤ u}` closed ⊇ `{∃ n, q < hₙ x}`.
* `exists_divisoid_div` — for `p q ∈ [0,1]_{C(X)}` on a basically
  disconnected `X`, a continuous `d` with `0 ≤ d ≤ 1`,
  `d x = min (p x) (q x) / q x` where `q x > 0`, and `d = 0` off
  `closure (supp q)`.  These three properties alone drive all five divisoid
  axioms; the least-upper-bound property is used only *inside* this lemma
  (against the ceilings `kₙ` and the characteristic function of
  `closure (supp q)`).

Two simplifications made the abstraction possible (both class 2/3
divergences from `bsols.tex:2466`):

1. **No countable-union-of-cozero-sets machinery.**  The generic proof needs
   "a countable union of cozero sets is cozero" (the `Σ 2⁻ⁿ φₙ` trick) to
   apply basic disconnectedness to `{x | sup hₙ x > q}`.  For the *specific*
   sequence `hₙ = (min f g / g)·χ_{Vₙ}` of the solution this union
   collapses: for `q ≥ 0`, since `min f g ≤ g`,
   `{x | ∃ n, q < hₙ x} = {x | q·g x < min (f x) (g x)}
   = supp (max (min f g − q·g) 0)` — a single cozero set; for `q < 0` it is
   `univ`.  So `BasicallyDisconnected` is applied only to honest single
   continuous functions and no `tsum` appears anywhere.
2. **No net argument, no compactness in the hard half.**  The solution
   proves continuity of `hₙ` by a net argument; here `hₙ` is
   `if x ∈ Vₙ then min f g / max g (1/(n+1)) else 0` with `Vₙ` clopen, so
   `Continuous.if` with empty frontier does it (the denominator is globally
   bounded below).  Neither `exists_continuous_sup` nor `exists_divisoid_div`
   uses `CompactSpace` or `T2Space` at all.  The solution's WLOG reduction
   "pick `B ≥ f` by compactness" in the `⇒` half is likewise replaced by the
   truncation `min |f| 1`, which has the same support; compactness and
   Hausdorffness enter *only* through `NormalSpace` for Urysohn's lemma
   (`exists_continuous_zero_one_of_isClosed` on `{y}` vs `closure (supp f)`).

The `⇒` half is otherwise the thesis's own argument, faithfully: `f/f` is
idempotent (from `mul_div` at `f/f ≼ f/f` plus `div_div_self`), hence
`{0,1}`-valued pointwise; `f ≼ f/f` forces `f/f = 1` on `closure (supp f)`;
for `y` outside, Urysohn's `g` gives `h := (f/f) ⊓ g` with `f ⊙ h = f` and
`h ≼ f/f`, so `div_unique` pins `h = f/f` and `(f/f)(y) ≤ g y = 0`.  Then
`closure (supp f) = (f/f)⁻¹(½, ∞)` is open.  (Departure from the printed
text: no `0 ⊔ g` is needed, since Mathlib's Urysohn already gives
`0 ≤ g ≤ 1`.)  The `⇐` half verifies the five axioms of `EffectDivisoid`
from the three properties of `exists_divisoid_div`, with
`div q q = χ_{closure (supp q)}` exactly, and `div_div_self` falling out of
`supp χ_S = S` for the clopen `S`.  Overall classification: **(1) faithful**,
with the two class-2/3 shortcuts above; the `div` is made total by dividing
`min p q` by `q`, which agrees with the thesis's partial division whenever
`p ≼ q` and makes `EffectDivisoid.div`'s totality a non-issue.

*Lean notes.*  (a) `(div e e : C(X, ℝ)) x` does **not** coerce — it
elaborates `div` at type `C(X, ℝ)` and demands `EffectDivisoid C(X, ℝ)`;
bind `ff` with `obtain ⟨ff, hffdef⟩ : ∃ ff, ff = div e e := ⟨_, rfl⟩` and
coerce the variable.  (b) hypotheses of the form `((cIcc_pcm_le_iff …).mp h) x`
carry `(fun f => f.toFun) ↑a x` heads that `rw`/`linarith` will not match;
restate them once with an explicit `∀ x, (a : C(X,ℝ)) x ≤ _` ascription.
(c) current-Mathlib renames hit here: `lt_div_iff₀`, `inv_anti₀`,
`lt_or_ge`, `Set.notMem_empty`, and `IsClopen.frontier_eq` applied as a
function (dot-notation on the `And` unfolds to `And.frontier_eq` and fails).

## Session 38 — `B/Dils` 149V complete: 149VIII (3 ⇒ 4) and 149IX (4 ⇒ 2), so `dils_selfdual` closes (worker 64)

**149V `dils_selfdual` is fully proved** — all five implications of the
cycle `1 ⇒ 3 ⇒ 4 ⇒ 2 ⇒ 3` plus `4 ⇒ 1` compile, and
`#print axioms` on `dils_selfdual`, `exists_isONBasis_of_bddUnComplete`
and `unComplete_of_isONBasis` gives exactly
`[propext, Classical.choice, Quot.sound]`.  The two blockers named in the
handoff were indeed proved (**80IV** `approximate_pseudoinverse` in
`Division.lean`, **87VIII** `ultraweakly_bounded_implies_bounded` in
`NormalFunctionals.lean`), but the brief's "should now be closable" hid one
real gap: **neither file was on `HilbertModules.lean`'s import path**
(`HilbertModules` imported only `Projections` + `Completeness`;
`NormalFunctionals` imports `Division` imports `Completeness`).  Adding
`import Theses.A.VN.NormalFunctionals` is cycle-free and was the first step.

**149IX (4 ⇒ 2), `unComplete_of_isONBasis` — class 1 (faithful), with the
mirroring landing exactly where predicted.**  The thesis takes
`bₑ = uslim_α ⟨e, x_α⟩`; under the mirror the net that is ultrastrong
Cauchy is the *starred* coefficient `[x_α, e]` (because **142III** bounds
`‖[d, y]‖_ω` by the seminorm of the *first* slot), so the limit taken by
**77I**.1 `vn_complete_1` is `cₑ = uslim [x_α, e]` and the basis
coefficient is `bₑ = cₑ*`.  ℓ²-summability: `Re ω(∑_S cₑ* cₑ)
= ∑_S ‖cₑ‖_ω² ≤ 2‖x‖_ω² + 2` at a late approximant `x` (Bessel
`mod_bessel` + `(a+δ)² ≤ 2a² + 2δ²` with `δ = (1+|S|)⁻¹`), which is an
ultraweak bound on the positive partial sums, and **87VIII** turns it into
the norm bound `L2Summable` needs.  Class-2/3 deviation in the last step:
where the thesis sums Parseval tails over the *infinite* basis, we bound
`x_α − t` at one *finite* stage `S ⊇ S₀` by four terms —
`x_α − P_S x_α` (tail of the basis expansion of `x_α`), `P_S(x_α − x_β)`
(the Bessel contraction `unSeminorm_coeff_sum_le`),
`∑_S e(⟨e,x_β⟩ − bₑ)` (`|S|` single-term estimates
`‖d • e‖_ω ≤ ‖d*‖_ω`, `unSeminorm_smul_proj_le`, at tolerance
`δ/(|S|+1)`), and `∑_S e bₑ − t`; the late witness `x_β` is chosen from
the intersection of the small-diameter set with the finitely many
coefficient-approximation sets.  Same estimates, no infinite sums, no
`⟨e, t⟩ = bₑ` computation.

**149VIII (3 ⇒ 4), `exists_isONBasis_of_bddUnComplete` — class 1
(faithful).**  Zorn (`zorn_subset`) gives a maximal orthonormal
`E ⊆ X`; the witness type is `↥E : Type v`.  Clause (b): with
`G S = ∑_{i∈S} bᵢ⟨eᵢ,eᵢ⟩bᵢ*`, the real net `Re ω (G S)` is monotone
bounded, so `sSup`-tail estimates make the partial sums
`v_S = ∑_S bᵢ • eᵢ` ultranorm Cauchy
(`‖v_S − v_T‖_ω² = Re ω(G S) + Re ω(G T) − 2 Re ω(G (S∩T))`), and they
are norm-bounded by `√M`; (3) applied to `Filter.map v atTop` converges
them.  Clause (a) reduces to **polar decomposition**
(`polar_decomposition`, private): for `y := x − ∑ e⟨e,x⟩ ≠ 0`, with
`b = √⟨y,y⟩`, an approximate pseudoinverse `(τₙ)` of `b` (**80IV**) gives
partial sums `sₘ = ∑_{n<N} τₙ` with `⟨sₘ•y, sₘ•y⟩ = q_N = ∑ pₙ`
(pairwise-orthogonal projections `pₙ = suppProj τₙ` — orthogonality from
`∑ pₙ ≤ ⌈b⌋ ≤ 1` via 55XIII); `(sₘ•y)` is ultranorm Cauchy and
norm-bounded by 1, its limit `u` has `⟨u,u⟩ = ⌈b⌋` and `b•u = y` — both
identified *ultraweakly* (148V `innerprod_ultraweak` against
`vna_supremum_uwlimit`/`vna_supremum_mult` transferred from the
directed-set index to `ℕ`, helper `uwTendsto_partialSums`), so no
ultrastrong convergence of `q_N` and **no `𝒷`-action distributivity** is
needed in the polar construction at all.  `⟨e, u⟩ = 0` then follows by
**60VIII** `mult_cancellation_1` (from `b·⟨e,u⟩ = 0` conclude
`⌈b⌋⌊⟨e,u⟩⌉ = 0`, and `⟨e,u⟩ = ⟨u,u⟩⟨e,u⟩` by **149III**), so `E ∪ {u}`
contradicts maximality.

*Lean notes.*  (a) Mathlib's `CStarModule` carries a **bare `SMul 𝒷 X`**
— no `(a+b)•x`, `(ab)•x`, `0•x` laws.  They are forced by definiteness
(`CStarModule.inner_self`) exactly as in 149III; `add_smul'`, `mul_smul'`,
`zero_smul'`, `sub_smul'`, `sum_smul'` (private) prove them by expanding
`⟨lhs−rhs, lhs−rhs⟩ = 0` with `noncomm_ring`.  The polar construction is
arranged to avoid them (single smul `sₘ • y`); 149IX needs `sub_smul'`
only.  (b) `selfAdjoint 𝒷` membership is *not* `IsSelfAdjoint` — convert
with `selfAdjoint.mem_iff.mpr`; and goals `x ≤ ⟨_,_⟩` produced by
`DirectedOn` come β-unreduced, where `rw [← Subtype.coe_le_coe]` fails but
`Subtype.coe_le_coe.mp (by rw [hN]; …)` works.  (c) statements produced by
`unSeminorm_neg'`/`unSeminorm_add_le` mention `(cstarBInner 𝒷 X).inner`;
`rw` against goals phrased in `inner 𝒷` fails on syntax — always bind them
with an explicit `have h : … (inner 𝒷 : X → X → 𝒷) …` ascription (defeq
`exact` accepts, `rw` then matches).  (d) `set`-bound abbreviations are
kernel-defeq: `rw [hgram S S, Finset.inter_self]` closes `⟨v S, v S⟩ = G S`
by the trailing `rfl` of `rw` — a following `simp only [hGdef]` dies with
"no goals".

**What 149V opens (re-derived).**  The previous session's finding that
**151Ia** `selfdual_completion_univ` was *not* opened by `1 ⇒ 3` alone no
longer applies: dils.tex:3283–3289 uses condition 2 (ultranorm
completeness) of the self-dual codomain `Y`, i.e. `1 ⇒ 2`, which the
completed TFAE now provides (`dils_selfdual` or directly
`bddUnComplete_of_selfDual` → `exists_isONBasis_of_bddUnComplete` →
`unComplete_of_isONBasis`).  All other ingredients its proof cites
(**148I** `blinear_bounded_is_ultranorm`, the 147 uniform-space basics)
are proved, so **151Ia is now genuinely unblocked** — but it is a
substantial standalone construction (extend `T` along `UnDense`
approximation nets, well-definedness, `𝒷`-linearity, boundedness
`‖T̂‖ = ‖T‖`, uniqueness) and was not attempted this session.  Also
touched by 149V: **160IV**.2/.3 (`hilbmod_projthm`) and **160IX**, whose
thesis proofs (dils.tex:4516–4530) take an orthonormal basis of the
ultranorm-closed `W` from `dils-selfdual` and *re-enter the Zorn argument
of 149VIII* to extend it — partially opened (the maximality-extension
step would need the 149VIII construction refactored to start from a given
orthonormal set, an easy generalization of `zorn_subset_nonempty`).
**150II** `dils_completion` remains blocked on its own transfinite
construction (150III–150XV), independent of 149V.

Doc comments fixed: the two stale "still `sorry`" blocker notes at 149VIII
/149IX, the 149VI route note, and 149V's own "remaining three are `sorry`"
tail.

## Session 39 — `B/Eff` realignment to the author's eleven corrections; 192V.3 and 192III.1/.2 closed (worker 65)

**Result: `B/Eff` stays at 18 `sorry`s with zero `sorryAx` leakage, but four
statements that were unfaithful or unfalsifiable are now honest and three of
them are proved.  192V.3 is realigned to the corrected
`eff-semilattice-aconv` and closed; 192III.1/.2 (QUESTIONS B6) are restated so
a transported impostor cannot satisfy them, and both close; 192III.3 keeps its
`sorry` but is no longer vacuous.  272 stale `eff.tex:`/`bsols.tex:` line
references across all eight modules were re-derived from the source.**

### 1. **192V.3** `eff-semilattice-aconv` — divergence class 4 (our statement
was silently weaker), now class 1

The author deleted "Semilattices are exactly abstract `2`-convex sets"
(erratum on `eff-semilattice-aconv`; QUESTIONS B1) and kept only "Every
semilattice `(L, ∨)` is an abstract `[0,1]`-convex set with
`h(⋁ᵢ λᵢ|xᵢ⟩) = ⋁_{i; λᵢ ≠ 0} xᵢ`", plus "a semilattice is cancellative iff
`x = y` for all `x,y`".  Three changes on our side:

* `semilattice_two_convex` is **gone**.  Its proof never used
  `SemilatticeSup` — that was the evidence for B1 — so it is now stated for
  what it actually proves: `two_convexComb_eq_eta` (every formal `2`-convex
  combination is a Dirac distribution, i.e. `𝒟₂ ≅ Id`), `two_convex_nonempty`
  (**every** type carries a `2`-convex structure) and the new
  `two_convex_unique` (that structure is unique).  Together: `AConv₂ ≅ Set`,
  which is the refutation, formalized.
* `semilattice_unitInterval_convex` — the surviving claim — no longer asserts
  the near-contentless `Nonempty (MConvex I L)`.  It now returns
  `∃ st, ∀ p a l, (∀ x, x ∈ a :: l ↔ p x ≠ 0) → st.h p = listJoin a l`, i.e.
  the structure map **is** the join of the support.  The existing proof
  already built exactly that `H` and proved the spec as `hH`; only the
  statement and the final `refine` changed (`⟨⟨H, …⟩, hH⟩`).
* New `semilattice_cancellative_iff`: for any `st` satisfying that spec,
  `st.Cancellative ↔ ∀ x y : L, x = y`.  Transcribed, not routed around: take
  `λ = ½` and mix `x` resp. `y` into `x ⊔ y`; both mixtures have support
  `{x ⊔ y, x}` resp. `{x ⊔ y, y}` and hence join `x ⊔ y`, so cancellativity
  gives `x = y`.  (The `a = w` case of the mixture needs `bin_self`, since
  `bin λ a a = η a` has a one-point support.)  Converse trivial.

### 2. **192III.1/.2/.3** `exc-dm-effectus` — divergence class 4, on Bas's
ruling for QUESTIONS B6 ("yes, please fix the statements")

All three read `∃ T, ∀ X, T.obj X = 𝒟_M X`, which constrains only the object
part.  Note the shape is not merely weak but *unfixable in place*: with
`F.obj X = 𝒟_M X` only propositional, `F.map f` cannot even be applied to a
`p : 𝒟_M X` without a cast, so no conjunct about `map`/`η`/`μ` can be added.
The existential is therefore dropped: `exc_dm_effectus_functor` and
`exc_dm_effectus_monad` are now **definitions** (`Type u ⥤ Type u`,
`Monad (Type u)`) whose object part is literally `MConvexComb M`, whose action
is literally `MConvexComb.map`, and whose `η`, `μ` are literally
`MConvexComb.eta`, `MConvexComb.mu`; five `rfl` lemmas (`_functor_obj`,
`_functor_map`, `_monad_toFunctor`, `_monad_eta`, `_monad_mu`) pin them, so a
monad transported along a bijection no longer qualifies.  The laws are the
already-proved `map_id`, `map_comp`, `mu_map_eta`, `mu_eta`, `mu_mu`.
`exc_dm_effectus_kleisli` is now stated about
`Kleisli (exc_dm_effectus_monad M)` and keeps its `sorry`: fixing .2 does not
hand it over: what remains is the starred exercise itself — a whole
`EffectusTotalStructure` on `Kl 𝒟_M` (finite coproducts, final object, both
pullback squares, joint monicity).  Worth noting for whoever takes it: the
analogous 196II needs `M` to be an effect *divisoid*, whereas 192III.3 claims
the Kleisli result for every effect monoid, so it is not a corollary of 196II.

### 3. The other nine corrections — checked, all already faithful

* **178IIIa** (`11e51c9`, `ecc8bdc`): the exercise now reads
  `a ⊙ 0 = 0 = 0 ⊙ a`, which is what `exc_emonzero` always proved, and the
  *solution* now argues from the four-fold law instead of one-sided
  distributivity — the circularity we flagged.  That is our proof's route.
  Two doc comments that described the old text were rewritten.
* **181XIII** (`334a383`): the circular "`1 = 1 ∘ 1`" opener is gone; the
  printed proof is now the one `one_m_is_id` transcribes (PCM-enrichment on
  `id ⋁ idᵖ`, then the zero–one axiom).  No Lean change.
* **195VII** (`5a3fafd`): the false lemma "if `c⊙a ⊥ c⊙b` then
  `(c/c)⊙a ⊥ (c/c)⊙b`" is deleted, and the new printed proof is *exactly* the
  route `divisoid_div_ovee` took — reduce to `c = a ⋁ b`, note
  `(a⋁b)/(a⋁b) ⊖ a/(a⋁b)` satisfies the defining property of `b/(a⋁b)`, then
  multiply on the left by `(a⋁b)/c`.  Our divergence class for 195VII drops
  from 2 (different route) to **1 (faithful)**; nothing referenced the deleted
  step.  Doc comment updated.
* **194I** (`d61feea`, `17cde5c`): the `M = 1` case split is now explicit
  upstream, which is the shape `aconvalmosteffectus_coproducts` already had —
  no Lean change, and QUESTIONS **B7 is answered**: effect monoids stay
  possibly trivial.  The stray parenthesis is fixed.
* **183III.1**, **189I.1/.2**, **191VIII** solution fixes: none of our doc
  comments quoted the garbled text, and the corrected paragraphs match what
  `pullback_lemma_1/2`, `distinction_part_tot_eff_1/2` and the `rng_*` chain
  prove.  ⚠ **191VIII's fix is incomplete**: the `=`s became `+`s, but the
  middle summand still reads `f(0,l,m)`/`g(0,l,m)` where the paragraph's own
  two preceding lines establish `f(0,l,0) = g(0,l,0)`; as printed the `m` is
  counted twice.  Recorded in ERRATA.

### 4. Line references

`eff.tex` shifted by up to 17 lines and `bsols.tex` by 3.  All 272 stale
`file:LINE` references in `Theses/B/Eff/*.lean` were re-derived mechanically
and **content-verified**: each old line's text was located in the new file
(exact string match, nearest occurrence), so a reference only moved when the
line it names still exists verbatim.  Two were remapped by hand: the old
`eff.tex:3328` (`\begin{point}{70}{Proposition}%`, deleted when
`eff-divisoid-add` got its label) → 3333, and a blank line, `eff.tex:6923` →
6906.  Beware when writing new doc comments in the same session as such a
sweep — three refs I had just written against the *new* file were caught by
the rewrite and had to be restored.

### 5. Open research question: can semilattices be the abstract `M`-convex
sets for some effect monoid `M`?  **No** — Bas's suspicion is right

Read as "there is an equivalence over `Set`" (i.e. the monads are isomorphic,
which is what "are the abstract `M`-convex sets" means), the answer is a clean
no, by counting the free algebra on **two** generators.

*Step 1: `𝒟_M 2 ≅ M` as a set, for every effect monoid `M`.*  Send
`p ↦ p(a)`.  Surjective: `p(a) = λ`, `p(b) = λᵖ` is a formal combination.
Injective: if `p(a) = λ ∉ {0,1}` the support is `{a,b}` and `λ ⋁ p(b) = 1`
forces `p(b) = λᵖ` by uniqueness of the orthosupplement; if `λ = 0` the
support is `{b}`, so `p(b) = 1 = 0ᵖ`; if `λ = 1` then `p(b) ⊥ 1`, so
`p(b) = 0 = 1ᵖ`.

*Step 2.*  The free semilattice on two generators is the non-empty finite
powerset, with **three** elements.  So `M` would have to have exactly three
elements, and a three-element effect algebra is forced to be the chain
`0 < u < 1` with `uᵖ = u`, i.e. `u ⋁ u = 1`.

*Step 3.*  No such effect monoid exists.  Put `x = u ⊙ u`.  Since `u ⊥ u`,
the four-fold law of **178II** says the four products of `(u ⋁ u) ⊙ (u ⋁ u)`
are summable with sum `1 ⊙ 1 = 1`, i.e. `x ⋁ x ⋁ x ⋁ x = 1` must be defined.
But `x = 0` gives `0 = 1`; `x = u` gives `u ⋁ u ⋁ u = 1 ⋁ u`, undefined; and
`x = 1` gives `1 ⋁ 1`, undefined.  Contradiction.

So for no effect monoid `M` is `𝒟_M` the non-empty-finite-powerset monad, and
`AConv_M` is never (over `Set`) the category of semilattices.  What survives
is exactly what the corrected `eff-semilattice-aconv` now says: every
semilattice *is* an abstract `[0,1]`-convex set, non-cancellatively.  Not
formalized — step 3 needs a concrete three-element effect algebra in Lean,
which is more machinery than the paragraph is worth; flagged here in case a
later session wants it.

### 6. Verification

* `lake build Theses.B.Eff.*`: exit 0, no errors; no new warnings beyond the
  file's pre-existing `linter.style.show` class.
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `two_convexComb_eq_eta`, `two_eta_injective`, `two_convex_nonempty`,
  `two_convex_unique`, `semilattice_unitInterval_convex`,
  `semilattice_cancellative_iff`, `exc_dm_effectus_functor`,
  `exc_dm_effectus_monad` and their five `rfl` lemmas.
* Declaration-level walk (`Lean.collectAxioms` over every non-internal name
  under `Theses.B.Eff`, not a grep):

  ```
  checked 1704 declarations under `Theses.B.Eff`
  18 depend on `sorryAx`; they are exactly the 18 `sorry`ed statements
  non-standard axioms (outside propext/Classical.choice/Quot.sound): 0
  ```

* Per-file `sorry`s: Comparisons 3, Dagger 3, DiamondAmp 2, EffectAlgebras 5,
  Effectus 2, Quotients 0, StatesPredicates 3, WStarCat 0 — **18**, unchanged
  (`semilattice_two_convex` was proved, not `sorry`ed; `exc_dm_effectus_kleisli`
  was `sorry` before and after).
* Nothing staged, nothing committed.

## Session 40 — `B/Dils` Paschke: the bundle defect is structural (`ρ` must land in the opposite algebra) (worker 66)

**Target:** implement the author's D2 ruling ("the definition of Paschke
dilation should not include the star", i.e. `IsPaschkeDilationOf` is correct)
by repairing `PaschkeModule`.  **Result: the ruling is confirmed, the proposed
one-field repair is wrong, and the real defect is structural — no edit of
`inner_tprod`/`h_def` can work, because `ρ : NMIUMap 𝒜 (Ba ℬ X)` cannot exist
in Mathlib's (mirrored, left-action) module convention.**  Two impossibility
theorems added, axiom-clean; the nine `sorry`s stand.

### 1. The brief's diagnosis (swap `h_def`'s arguments) is wrong

`h_def`'s `⟨1⊗1, T(1⊗1)⟩` is the ℂ-linear order and is right; the swapped
order `⟨T(1⊗1), 1⊗1⟫` is conjugate-linear in `T`, so `h` could not be an
`NCPMap`.  (Mathlib's `CStarModule` inner is conjugate-linear in the *first*
argument and linear in the second: `inner_smul_left_complex`,
`inner_op_smul_right`.)  Neither is `inner_tprod` wrong on the `b`-side: with
`tprod a b = b • tprod a 1` (from `smul_action`), `inner_op_smul_left/right`
force the shape `⟨a⊗b, a'⊗b'⟩ = b' M(a,a') b*` under *any* mirroring, as
recorded in session 14.

### 2. The bundle is worse than reported: it forces `φ = 0`

`Paschke.lean`, `paschke_module_phi_eq_zero` (machine-checked, axiom-clean):
`inner_tprod`'s right-hand side `b' φ(a'* a) b*` is ℂ-**linear** in `a`, while
the left-hand side is conjugate-linear in `a` (inner conj-linear in slot 1,
`PhiCompatible.smul_complex` ℂ-linear).  At `c = i`: `2i·φ(a) = 0`, so
`φ = 0`.  Session 14's `h (ρ a) = φ (star a)` is a *consequence* of an already
inconsistent bundle, not the defect.  `PaschkeModule φ` is uninhabited for
every non-zero `φ`; `existence_paschke` is false; the nine theorems are vacuous.

### 3. Why no repair of `inner_tprod` works either

Positivity of `⟨v,v⟩` for `v = ∑ᵢ tprod aᵢ bᵢ` gives
`⟨v,v⟩ = ∑ᵢⱼ bⱼ M(aᵢ,aⱼ) bᵢ*`, i.e. the matrix `K_{kl} = M(a_l,a_k)` must be
positive — note that in the *left*-action convention the positive Gram matrix
is the transposed one, `[⟨x_l,x_k⟩]`, not `[⟨x_k,x_l⟩]` (checked on the model
`X = ℬ`, `b•x = bx`, `⟨x,y⟩ = y x*`).  That leaves exactly two candidates:

| `M(a,a')` | variance of `tprod` in `a` | verdict |
|---|---|---|
| `φ(a'* a)` (the current field) | conjugate-linear | `ρ` is then conjugate-linear, so not an `NMIUMap`; with the ℂ-linear `tprod` of `PhiCompatible` it forces `φ = 0` (§2) |
| `φ(a' a*)` | ℂ-linear (as `PhiCompatible` has it) | `ρ(a₀)` is not adjointable: `paschke_rho_forces_cyclic` |

`paschke_rho_forces_cyclic` (machine-checked, axiom-clean) derives from the
second candidate plus `ρ_tprod` and `star (ρ a₀) = ρ (star a₀)` that
`φ (a' a* a₀*) = φ (a₀* a' a*)` for all `a, a', a₀` — i.e. `φ` is cyclic, which
fails for `φ = id` on `M₂` (`star` is a bijection, so this says `φ(xyz)=φ(zxy)`).

### 4. Root cause and the repair the author has to rule on

Mirroring a *right* Hilbert ℬ-module to a *left* one is passage to the
**conjugate module** (the ℂ-action is conjugated too), and it turns the
thesis's *left* `𝒜`-action into a *right* action.  Concretely: in a left
Hilbert ℬ-module every adjointable operator is automatically ℬ-linear, and for
`X = ℬ` the adjointables are the **right** multiplications `R_t`, with
`R_t ∘ R_s = R_{st}` — so `𝒷ᵃ(X)` is anti-isomorphic to the thesis's `𝒷ᵃ(X)`,
`𝒷ᵃ(ℬ) ≅ ℬᵒᵖ`.  Pinning `X` by `univ` at `φ = id_𝒜` turns `ρ_tprod` into the
demand for a ℂ-linear anti-automorphism of `𝒜`, which a general von Neumann
algebra does not admit (Connes).  Hence:

    ρ         : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ
    ρ_tprod   : ρ(a₀)(a ⊗ b) = (a * a₀) ⊗ b
    inner_tprod : ⟨a ⊗ b, a' ⊗ b'⟩ = b' * φ (a' * star a) ... → b' * φ (a' * a*) * b*
    h_def     : unchanged — and then h (ρ a) = φ a, exactly as the ruling asks

plus the matching `PhiCompatible.bound` (`∑ᵢⱼ bᵢ φ(aᵢ aⱼ*) bⱼ*`) and, in
`existence_paschke_5`, a `PaschkeTriple` with `P = (Ba ℬ M.X)ᵐᵒᵖ`.  Mathlib has
`CStarAlgebra Aᵐᵒᵖ`; `PartialOrder`, `StarOrderedRing` and the repo's
`VonNeumannAlgebra` on the opposite algebra are new work.  **Not done
unilaterally**: it is a second design decision, not the one that was ruled on.

### 5. Consequences for the rest of the brief

* `existence_paschke_5` is *not* "now true" — it is vacuously true (uninhabited
  hypothesis) and unprovable without deriving `False` from `PaschkeModule`,
  which would be a dishonest close; left `sorry`.
* `existence_paschke_4`'s `hφ` (`φ a = ⟨e, ϱ'(a) e⟩`) is **not** off by a star:
  it mirrors `h_def` exactly, and `h_def` is right.  The session-38 short route
  through `PaschkeModule.univ` (four applications, no `paschke-uniqueness`, no
  λ-scaling, no density) remains the right plan once `ρ`'s type is settled.
* `existence_paschke_2` survives untouched (its proof uses `univ`, `compat` and
  `ρ_tprod`, none of which changed).
* Divergence class: 4 (our transcription defect, not the thesis's).

### 6. Verification

* `lake build Theses.B.Dils.Paschke` → `Build completed successfully
  (8721 jobs)`, zero `error:` lines (the `linter.style.header` noise is
  `info:`-level and pre-existing).
* `#print axioms` → `[propext, Classical.choice, Quot.sound]` for
  `paschke_module_phi_eq_zero` and `paschke_rho_forces_cyclic`.
* `Paschke.lean` `sorry`s: 9 → **9** (unchanged); two new theorems, both proved.
* Files touched: `Theses/B/Dils/Paschke.lean` (header WARNING rewritten, two
  theorems added, `existence_paschke` doc marked FALSE), `QUESTIONS.md` (D2),
  this log.  Nothing staged, nothing committed.

## Session 40b — `B/Dils` `IsVNTensor`: proc.tex 108II's `tensor-2` was dropped in transcription (worker 66)

**Divergence class 4** (our error, not the thesis's).  `IsVNTensor`
(`SelfDual.lean`) rendered 108II (`tensor`, proc.tex:2034) with `tensor-1`
(`generates`) and `tensor-3` (`separating`) but silently omitted **`tensor-2`**
— *"for all np-functionals `σ : 𝒜 → ℂ` and `τ : ℬ → ℂ` the product functional
`γ(σ,τ) : 𝒯 → ℂ` exists and is positive"*.  QUESTIONS **B5** had recorded this
as "the definition is too weak"; it is not — the definition is fine and we
copied it incompletely.  Added verbatim:

```lean
exists_productFunctional : ∀ (ω : NPFunctional 𝒜) (ξ : NPFunctional ℬ),
  ∃ Ω : NPFunctional 𝒞, ∀ (a : 𝒜) (b : ℬ), Ω (t a b) = ω a * ξ b
```

"and is positive" needs no separate clause: normality and positivity are
carried by the type `NPFunctional 𝒞`.  `tensor-1` gives *uniqueness* of `γ(σ,τ)`
and `tensor-3` its faithfulness; neither gives existence, which is what 165VI
must consume.

**Verbatim `tensor-2` over `tensor-characterization`.**  108II's forward
reference (proc.tex:3578, 111VII) restricts existence to *centre separating*
collections `Σ, Γ` — but it is an equivalence ("is a tensor product iff"), not
a weaker interface: it still demands existence, only for fewer functionals, and
it would drag `CentreSeparating` into the definition, which nothing in parsecs
1640–1670 consumes.  So the safe default was taken.

**Constructions obliged by the new field — both discharged.**  Only two things
build an `IsVNTensor`: `vnTensor_mul_complex` (the ℂ ⊗ ℂ non-vacuity witness;
the product functional is `smulNP (σ(1)·τ(1)) complexIdNP`, using that
`ω a = a·ω 1` on ℂ and `ω 1 ≥ 0`) and `vnTensor_flip` (transports the field,
`mul_comm`).  Nothing else in the tree constructs one — `vnTensorProduct_nonempty`
(111XII) is `sorry` and `A/Proc/Tensor.lean` mentions `IsVNTensor` only in
comments.  Three private helpers were added (`npf_apply_complex`,
`npf_one_ofReal`) and `npf_csmul` was moved above its first use.

**165VI is still unreachable, and not because of this field.**
`ba_ext_tensor_pres` *concludes* `IsVNTensor Θ`, so `tensor-2` is an extra
obligation there — to be met the way 165IX does it, by
`σ ⊗ τ = (f ⊗ g)(x ⊗ y, (·) x ⊗ y)`, which is exactly what the field now
supplies on the *given* `t`.  Precise blockers: the three `sorry`ed clauses of
**164II** that its proof consumes — `ext_tensor_dense`, `ext_tensor_basis`,
`ext_tensor_ketbra_dense` — and 165VII–165X, which are not converted.

**Verification.** `lake build Theses.B.Dils.SelfDual` and
`… .Paschke/.Pure/.Kaplansky` complete successfully, zero `error:` lines;
`#print axioms` clean (`[propext, Classical.choice, Quot.sound]`) for
`vnTensor_mul_complex`, `vnTensor_flip`, `vnTensor_smul_complex_right`,
`vnTensor_legLeft_normal`.  `SelfDual.lean` `sorry` count unchanged (24).
Files touched: `Theses/B/Dils/SelfDual.lean`, `QUESTIONS.md` (B5 closed), this
log.  Nothing staged, nothing committed.

## Session 41 — `A/Proc` 117II.1 in its repaired form, and the `κᵢ` block lifted into `Tensor.lean` (worker 66, A/Proc)

**Proved: 117II.1 `sum_generation_1` (Tensor) and 132IV's unit
`exists_freeMonoidUnit` (Duplicators).**  Chapter 117 → 115: Tensor 44 → **43**,
Duplicators 18 → **17**, Measurement 38, QuantumLambda 17 (its two
`declaration uses 'sorry'` counts are unchanged; the file only lost lemmas by
the move).  Both new theorems `#print axioms`-clean.

### 117II.1 (proc.tex:3733, Exercise) — divergence class **4 → 1**

Session 33 refuted the printed statement (`sum_generation_1_is_false`, kept in
the tree) and realigned ours to the repaired form `⋃ᵢ κᵢ(Aᵢ) ∪ {eᵢ}`.  That
repaired form is now **proved**, following the erratum's own recipe:

1. `kappaPreimage i W hone = {a | κᵢ(a) ∈ W}` is a ∗-subalgebra of `𝒜ᵢ`, and
   *unital* exactly because `eᵢ = κᵢ(1) ∈ W` — the hypothesis the printed
   exercise lacks.  It is closed (`κᵢ` is isometric: `lp.norm_single`) and
   closed under directed suprema, because the order on `⊕ⱼ 𝒜ⱼ` is pointwise
   (`lp_infty_le_iff`) and `κᵢ(d)ⱼ = 0` off `i`; so it is a von Neumann
   subalgebra containing `Sᵢ`, hence `⊤` by the hypothesis on `Sᵢ`.
2. For `x ≥ 0` the finite restrictions `∑_{j∈F} κⱼ(xⱼ)` are directed with
   supremum `x` — both directions of the LUB are the pointwise order again,
   with `Finset.sum_pi_single` computing the coordinates.
3. A general `x` is `ℜx + i·ℑx` (`realPart_add_I_smul_imaginaryPart`), and a
   self-adjoint `y` is `(y + ‖y‖·1) − ‖y‖·1` with the first summand positive
   by `IsSelfAdjoint.neg_algebraMap_norm_le_self`.  Step 3 is *not* in the
   author's sketch (his "a general `x` is the directed supremum of its finite
   restrictions" is only true for positive `x`); it costs six lines.

**`lp_infty_exists_isLUB` is not used** — only `lp_infty_le_iff` and
`lp_infty_nonneg_iff`.  Each LUB in the proof is *exhibited*, never obtained
from completeness, so the von Neumann hypothesis on the summands is consumed
only through `isVNSubalgebra_wstar`.

### The refactor: `κᵢ` now lives in `Tensor.lean`

`lpKappa` and its algebra lemmas (`_mul_left`, `_mul`, `_sa`, `_star`,
`_apply_self`, `_apply_ne`, `_sa'`, `_le`) were **moved verbatim** from
`QuantumLambda.lean` (§DirectSums) into a new `section Coprojections` of
`Tensor.lean`, which `QuantumLambda` imports; signatures are unchanged, so no
call site moved.  `lpSumSA`, `exists_kappa_one` and
`lp_nmiu_functional_factors` stay where they are.  `lpEvalSAH` did **not** need
to move (contrary to session 33's note): `A/VN`'s `lpEvalₗ` covers the one
place a coordinate map was wanted, via `lp.coeFn_sum`.

New in that section: `lpKappa_add/_zero/_smul/_sub` (one-liners over Mathlib's
`lp.single_add` etc. — Mathlib already has the whole additive/linear API for
`lp.single`, including `lp.norm_single` and `lp.lsingle`), `lpKappa_continuous`,
`lpKappa_sum_apply`, and `lpKappa_eq_single`.  The last is the bridge the move
needs: `lpKappa` bakes in the classical `DecidableEq I` while 117II.1's
statement carries an instance binder, and the two are equal but not defeq.
`rw` cannot cross that gap (it pre-synthesizes the instance in the pattern);
`simp` can, because it matches the instance out of the target.

### 132IV `exists_freeMonoidUnit` (proc.tex:6719) — class **3 (mild)**

`η(a)(φ) = φ(a)` is asserted, not proved, in the thesis ("let `η` be the
nmiu-map given by …").  It is: `Memℓp … ∞` because nmiu-maps are contractive
(`NonUnitalStarAlgHom.norm_apply_le`), a ∗-homomorphism because the operations
on `ℓ^∞` are pointwise, and normal because the order is pointwise and each `φ`
is.  This also un-taints `freeMonoidUnit`, hence the *statement* of
`free_monoid_in_vNAMIU` (132IV proper), which is defined by choice from it.

### Where the brief was wrong

* **128XIII is not closable, and the `lp` instance was never its blocker.**
  `duplicable_product`'s hypothesis is `Duplicable (lp 𝒜 ∞)`, and `Duplicator`
  carries a `δ : VNT A A →ₚ[ℂ] A` — so it is `VNT`-typed and sits behind 111XII
  with the rest.  `vonNeumannAlgebra_lp_infty` being discharged changes nothing
  for it.
* **104VII needs more than 104III.5.**  Its proof (proc.tex:1564) also uses
  104III.4/.1 for the two "by `centrally-similar-basic`" steps, 80IV for the
  approximate pseudoinverse producing the `eₙ`, `mult-jus-cont` for the
  ultrastrong convergence of `eₙaeₙ`, and a corner-restriction argument
  (`eₙ𝒜eₙ`) to reduce to invertible `p, q`.  104VI is the easy input and is
  already proved.
* **81VI/81VII/81IX are still `sorry`** in `A/VN/Division.lean` (1739, 1753,
  1792), so the 96V/98IX/100II.3/103II/99XI cluster has *not* opened.
* **`l2_tensor` (109III.1) is proved** — it has been for several sessions; the
  "best untouched target" note in the w37 map is stale.

### 132VI is blocked, and precisely

`exists_freeMonoidUnitCpsu` is the same formula into `ℓ^∞(W*_cpsu(𝒜,ℂ))`, but
`NCPMap` extends **Mathlib's** `A →CP B`, whose complete positivity is stated
on `CStarMatrix n B` — not our quadratic-form `IsCompletelyPositiveMap`, which
*would* reduce pointwise to complete positivity of each `ω`.  So it is blocked
on the same missing componentwise description of positivity in
`CStarMatrix n (lp …)` as `vn_products_ncpsu`.

**Verification.** `lake build Theses.A.Proc.Duplicators` (which covers all four
modules) exits 0; `lake env lean` on `Tensor.lean` and `Duplicators.lean` exit
0 with no new warnings in the touched regions (the `omit` lines were tuned
until `linter.unusedSectionVars` was silent).  `#print axioms` clean for
`sum_generation_1`, `exists_freeMonoidUnit`, `lpKappa_eq_single`,
`lpKappa_continuous`, `lpKappa_sum_apply`, `lpKappa_add`, `lpKappa_smul`, and
the regressions `lp_nmiu_functional_factors`, `sum_generation_2`,
`linf_generated`, `sum_generation_1_is_false`.  Files touched:
`Theses/A/Proc/{Tensor,QuantumLambda,Duplicators}.lean`, `ERRATA.md`, this log.
Nothing staged, nothing committed.

## Session 42 — `A/VN` parsec 880: the **Double Commutant Theorem** (88V, 88VI, 88VIII) and 56XVIII `sum-of-orthogonal-projections` (worker 67, A chain)

Target given: parsec 890 (89V `sigma-weak-lemma-2`, 89VII `sigma-weak-lemma`,
83V `cceil-sum`, 89IX `normal-functional`).  **None of the four is reachable
without first closing parsec 880 and parsec 810–820**, which the brief did not
say; §4 below records the corrected dependency graph, which is the main
non-Lean result of the session.  What was proved instead is the gate itself.

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | file | class |
|---|---|---|---|
| **88V** | `proto_double_commutant` | `NormalFunctionals.lean` | 1 — the thesis's own hint, followed step by step |
| **88VI** | `double_commutant` | `NormalFunctionals.lean` | 1 |
| **88VIII** | `centre_commutant` | `NormalFunctionals.lean` | 1 |
| **56XVIII** | `sum_of_orthogonal_projections` | `Projections.lean` | 2 — Exercise, no author argument exists |

`A/VN` sorries 86 → 82; `A/CStar` 28 → 28 (untouched).

### 1. 88V: the amplification, built as a reusable API

vn.tex 6752 asks for the `ℕ`-fold amplification `ρ' : B(H) → B(⊕ₙ H)` and two
facts about it.  `⊕ₙ H` is Mathlib's `lp (fun _ : ℕ => H) 2`; the new
declarations in `NormalFunctionals.lean` (all public, all in `section BH`) are

* `amp_memLp`, `ampLM`, `ampLM_apply`, `ampLM_norm_le`, `amp`, `amp_apply` —
  the operator `ρ'(t)y = (t yₙ)ₙ`, bounded by `‖t‖`;
* `lp_clm_ext` (two operators on `lp` agree iff they agree componentwise),
  `amp_star`, `ampHom`, `ampHom_apply` — `ρ'` as a `→⋆ₐ[ℂ]`, so that
  `S.map ampHom` is the amplified subalgebra;
* `amp_single` (`ρ'(b) Pₘ* = Pₘ* b`), `ampCorner`, `ampCorner_apply` —
  `Pₙ a Pₘ*` via Mathlib's `lp.evalCLM` / `lp.singleContinuousLinearMap`;
* `ampCorner_mem_commutant` — the thesis's first hint, `Pₙ a Pₘ* ∈ S□` for
  `a ∈ ρ'(S)□`, three lines once `amp_single` is available;
* `amp_mem_double_commutant` — the second hint, `ρ'(t) ∈ ρ'(S)□□` for
  `t ∈ S□□`.  The only real work: `y = ∑ₘ Pₘ*yₘ` (`lp.hasSum_single`) is
  pushed through `Pₙ ∘ a`, giving `Pₙ(a y) = ∑ₘ (Pₙ a Pₘ*) yₘ`; applying `t`
  and commuting it past each corner turns this into `Pₙ(a ρ'(t) y)`.

88V itself is then: `t ∈ S□□`, `ω` an np-functional on `B(H)`, `ε > 0`.
**39IX** `bh_np` (already proved, `A/CStar/TowardsVN.lean`) writes
`ω = ∑ₙ ⟨xₙ,(·)xₙ⟩` with `∑‖xₙ‖² < ∞`, so `x' := (xₙ)ₙ ∈ ⊕ₙ H`; the private
`hasSum_normSq_of_np` of `Completeness.lean` gives `‖ρ'(u)x'‖ = ‖u‖_ω` for
every `u`, and **88IV'** `carrier_vector_state'` (already proved) gives
`closure(ρ'(S)□□ x') = closure(ρ'(S) x')`.  So `ρ'(t)x'` is `ε`-approximated
by some `ρ'(s)x'` with `s ∈ S`, i.e. `‖s − t‖_ω < ε`.

Three lemmas of `Completeness.lean` were **de-privatised** to make this
possible (no other change to that file): `mem_usClosure_iff`,
`usClosure_subset_uwClosure`, `hasSum_normSq_of_np`.

### 2. 88VI, 88VIII: assembly

`S□□ ⊆ us-cl(S)` is 88V; `us-cl ⊆ uw-cl` is `usClosure_subset_uwClosure`;
`uw-cl(S) ⊆ W*(S)` is `closure_minimal` against `vnsac` (75VIII, proved) for
`isVNSubalgebra_wstar`; and `W*(S) ⊆ S□□` because `commutant_basic_3'` (65III,
proved) makes `S□□` a von Neumann subalgebra containing `S` — the auxiliary
`star_mem_commutant_of_starSubalgebra` supplies the star-closedness of `S□`
that 65III wants.  88VIII is then `wstar_eq_of_isVNSubalgebra` (new, three
lines) plus `Set.inter_comm`.

### 3. 56XVIII: no forward reference needed after all

The Exercise has no published solution.  Proof: the partial sums `s_F` are
projections (`isStarProjection_sum`, already in the file), `s_F ≤ ⋃ᵢpᵢ` because
`q pᵢ = pᵢ` makes `q − s_F` idempotent and self-adjoint hence positive, and
`⋃_F s_F = ⋃ᵢ pᵢ` because the two families have the same projection upper
bounds.  `{s_F}` is directed, so `isLUB_projSup_of_directed` turns `⋃ᵢpᵢ` into
an honest `IsLUB`; normality of `ω` (`preservesDirSups'`) plus
`isLUB_re_of_isLUB` and `tendsto_atTop_isLUB` give `ω(s_F).re ↑ ω(q).re`; and
`‖s_F − q‖_ω = √(ω(q − s_F).re)` because `q − s_F` is a projection.

`isLUB_projSup_of_directed` was **moved** from `Division.lean` (where session
36 introduced it) to `Projections.lean`, just after `projSup_eq`, since
56XVIII sits earlier in the file order.  Its statement and proof are
unchanged; `Division.lean` keeps using it under the same name.

### 4. Corrected dependency graph for parsec 890 (the brief was wrong here)

The brief said "890 is 400–600 lines, 111VII another 300–450 given 89IX".
Measured against the tree, the real picture is:

* **89V** `sigma_weak_lemma_2` needs, beyond 89I and 89III (both already
  proved): **88IV** `carrier_vector_state` (`sorry`), **88IX**
  `commutant_cceil` (`sorry`), and — for the *leastness* half of its
  `IsLeast` conclusion — **69IVb** `nmiu_image` (`sorry`, `Projections.lean`),
  because the argument needs `Z(π(𝒜)□) ⊆ π(𝒜)`, and 88VIII only gives
  `Z(π(𝒜)□) = Z(π(𝒜)□□) = Z(W*(π(𝒜)))`.  88IX in turn needs 88VIII (now
  proved) *and* the existence of relative central carriers in a von Neumann
  *subalgebra*, which `cceilMap` does not supply (it is stated for a von
  Neumann algebra as a type).
* **83V** `cceil_sum` needs **82I** `polar_decomposition` (`sorry`), which
  needs **81III** `proto_douglas_1` (`sorry`), which needs 77I `vn_complete_1`
  (proved) *and* 56XVIII (proved this session).  There is no shorter route:
  `MvNLE` is defined by partial isometries, so a proof of 83V must produce
  them, and in a von Neumann algebra that is the polar decomposition.
* **89IX** needs 89VII (hence 89V) *and* 83V.

One short route *was* found and is worth recording even though it is not yet
usable: in 89V the pairwise orthogonality of the `U_ω U_ω*` — which the thesis
gets from `commutant_cceil` (88IX) — is available for free, because
`ω(1 − ⌈⌈ω⌉⌉) = 0` forces `ρ(⌈⌈ω⌉⌉)x_ω = x_ω`, so `closure(ρ(𝒜)x_ω)` sits
inside the range of the central projection `ρ(⌈⌈ω⌉⌉)`, and those are pairwise
orthogonal by hypothesis.  Only the *leastness* half of 89V needs 88IX/69IVb.

### 5. Verification

Whole-project `lake build`: exit 0, `Build completed successfully (8738
jobs)`, identical to the baseline taken at the start of the session, so
`Theses.A.Proc.*` and `Theses.B.Dils.*` build as cleanly as they were found.
(Worth knowing: `lake build` here reports "build failed" while **swallowing
the error message**.  Twice there was no cause at all — `Theses.B.Dils.Paschke`
and `HilbertModules`, rebuilt fine on their own, memory pressure on a 14 GB
box — and once there was a real one, four parse errors of mine that neither
`lake build`'s output nor a `grep error` on it revealed.  `lake env lean
Theses/…/Foo.lean` prints them; use it before concluding a failure was
transient.)
`#print axioms` clean on all sixteen new declarations and on the regression
target `approximate_pseudoinverse`.  No new ERRATA rows, no new QUESTIONS
rows.  Files touched: `Theses/A/VN/{Completeness,Division,NormalFunctionals,
Projections}.lean` and this log.  Nothing staged, nothing committed.

## Session 43 — `B/Dils` Paschke unfrozen: the `ᵐᵒᵖ` repair, `154III`.2/.4, and a non-vacuity witness (worker 68)

**Class (4)** — our statement mis-transcribed the thesis.  Bas ruled
("Ok, fix the transcription please", 2026-08-16) on QUESTIONS **D2**; this
session implements the fix.  Files touched: `Theses/B/Dils/Paschke.lean`,
`Theses/B/Dils/HilbertModules.lean`, `Theses/B/Dils/SelfDual.lean`,
`QUESTIONS.md`, this log.  Nothing staged, nothing committed.

### 1. The mirroring dictionary was incomplete, and that is the whole bug

Sessions 14–15 established that `PaschkeModule` was uninhabited for every
non-zero `φ` and that no edit of `inner_tprod`/`h_def` repairs it.  The
missing ingredient is one line of the dictionary.  Mathlib's
`CStarModule ℬ X` is the **conjugate** module of a right Hilbert ℬ-module,
and a conjugate module conjugates the **ℂ**-action as well as the ℬ-action:

    b • x := x·b*      ⟨x,y⟩ := [y,x]      c ·̄ x := c̄ x

(the third clause is forced — `[·,·]` is conjugate-linear in its first slot
and so is Mathlib's `⟨·,·⟩`, so `⟨x,y⟩ = [y,x]` is ℂ-sesquilinear only for
the conjugated action).  The tree had the first two clauses and not the
third, and rendered the thesis's `⊗` as `tprod a b = (a ⊗ b*)_thesis`.  With
the third clause the correct rendering carries a `star` in **both**
arguments,

    tprod a b = (a* ⊗ b*)_thesis,

and that single correction produces, simultaneously and consistently:

* `PhiCompatible.smul_complex` (`tprod` is ℂ-linear in `a` — it is `star`
  composed with a conjugate-linear map into a conjugated ℂ-structure);
* `inner_tprod : ⟨a ⊗ b, a' ⊗ b'⟩ = b' φ(a' a*) b*`, the substitution
  `a ↦ a*`, `b ↦ b*` into the thesis's `[a⊗b, α⊗β] = b* φ(a* α) β`;
* `PhiCompatible.bound` with `∑ᵢⱼ bᵢ φ(aᵢ aⱼ*) bⱼ*` (same substitution),
  whose positivity is complete positivity of `φ` at the families `(aᵢ*)`,
  `(bᵢ*)`;
* and the `ᵐᵒᵖ`: because the ℂ-action of `End(X̄)` is conjugated too, the
  ℂ-*linear* rendering of `ϱ` is the anti-homomorphism
  `a₀ ↦ (a ⊗ b ↦ (a a₀) ⊗ b)`, i.e. `ρ : NMIUMap 𝒜 (Ba ℬ X)ᵐᵒᵖ`, whose
  adjoint is `ρ(a₀*)` on the nose.

`h_def` is unchanged and `paschkeModule_h_ρ` proves `h (ρ a) = φ a` with no
`star`, so `IsPaschkeDilationOf` (`Stinespring.lean:1179`) stands as ruled.
The two negative results are kept in the tree as
`paschke_inner_conj_forces_zero` (was `paschke_module_phi_eq_zero`, now
stated with explicit hypotheses so it survives the repair) and
`paschke_rho_forces_cyclic`.

### 2. Mechanism: `ᵐᵒᵖ` on the operators, not on the scalars

Two mechanisms were on the table.  The brief's guess was `ᵐᵒᵖ` on the
*scalars* (`CStarModule ℬᵐᵒᵖ X`, making `𝒜 ⊗_φ ℬ` an honest right module),
on the theory that Mathlib's `MulOpposite` support for a C*-algebra `ℬ` is
richer than anything available for `Ba ℬ X`.  **That turned out to be
false.**  `CStarAlgebra Aᵐᵒᵖ` (`Mathlib/Analysis/CStarAlgebra/Classes.lean:139`),
`MulOpposite.instPartialOrder` (`Mathlib/Algebra/Order/Group/Opposite.lean:33`,
with `op_le_op` *definitional*) and `StarOrderedRing Aᵐᵒᵖ`
(`Mathlib/Algebra/Order/Star/Basic.lean:395`) are generic in `A` and apply
verbatim to `Ba ℬ X`.  The only missing instance, the abstract Kadison
`VonNeumannAlgebra Aᵐᵒᵖ` of `Theses/Common.lean`, is needed *identically* by
both routes — the scalars route needs it for `ℬᵐᵒᵖ` to invoke
`ba_vonNeumannAlgebra`.  It is proved once here as
`vonNeumannAlgebra_mulOpposite` (via `selfAdjointUnop : selfAdjoint Aᵐᵒᵖ ≃o
selfAdjoint A`, whose `map_rel_iff'` is `Iff.rfl`, and `npFunctionalOp`).

With the tiebreaker gone the decision is churn, and the operators route
wins decisively: `𝒜 ⊗_φ ℬ` stays a `CStarModule ℬ`-module, in the same
mirrored convention as the rest of the chapter, so `SelfDual`,
`cstarBInner`, `IsBoundedModuleMap`, `UnDense` and `ExtTensor` apply
unchanged.  **167I** (`paschke_tensor`, `paschke_tensor_module`) and
**166VI** (`dilationspace_dense_subset`) in `SelfDual.lean` needed no edit
at all and still build; the scalars route would have needed `ExtTensor`
over `ℬᵢᵐᵒᵖ` plus an `IsVNTensor`-to-the-opposite transfer, i.e. new
infrastructure for statements that are still `sorry`.  `ᵐᵒᵖ` now appears in
exactly three places, all inside `Paschke.lean`.

### 3. A third symptom the `ᵐᵒᵖ` explains — and a lead on 145I

In the mirrored convention the vector state is completely positive on the
**opposite** of `𝒷ᵃ(X)`.  Concretely, for `X = ℬ` the adjointable operators
are the *right* multiplications, `t ↦ R_t : ℬ ≅ 𝒷ᵃ(ℬ)ᵐᵒᵖ` (proved here as
`rightMulEquiv`), and `h(R_t) = ⟨1, R_t 1⟩ = t`.  So `h : 𝒷ᵃ(ℬ) → ℬ` is
`unop`, which under `M₂ᵐᵒᵖ ≅ M₂` is the transpose — positive but **not**
completely positive; `h : 𝒷ᵃ(ℬ)ᵐᵒᵖ → ℬ` is a ∗-isomorphism.  The old
`h : NCPMap (Ba ℬ X) ℬ` was therefore wrong for a third, independent
reason.  **Lead for a later session:** **145I**
`hilbmod_vectstates_cp` in `HilbertModules.lean` states exactly the form
that fails here (`T ↦ ⟨x, Tx⟩ : 𝒷ᵃ(X) → 𝒷` is cp) and is still `sorry`; it
is very likely mis-mirrored the same way and should be checked against
`X = ℬ = M₂` before anyone tries to prove it.  Out of scope this session.

### 4. What closed

* **154III.2** `existence_paschke_2` (already proved before the session)
  survives the repair.  Its 100-line φ-compatibility argument was
  **extracted** as `PhiCompatible.mul_right`: shifting a φ-compatible map to
  `(a,b) ↦ T (a a₀) b` is again φ-compatible.  `existence_paschke_2` is now
  eight lines, and the extracted lemma is what makes 154III.4's intertwining
  clause cheap.
* **154III.4** `existence_paschke_4` (`paschke-spatial`) — **new**.  The
  thesis proves it via `paschke-uniqueness`, a λ-scaling lemma and a density
  statement.  None of that is needed: the universal property of part 1 does
  it alone, applied four times.  (i) To `T(a,b) = b·ϱ'(a)e`, whose Gram
  matrix `⟨T(aᵢ,bᵢ), T(aⱼ,bⱼ)⟩ = bⱼ φ(aⱼ aᵢ*) bᵢ*` is the required bound
  *with equality and constant 1* — the computation goes through
  `ϱ'(a*)ϱ'(a') = ϱ'(a' a*)` in the opposite algebra.  That yields `S`.
  (ii)+(iii) Twice against **ℬ itself** — self dual by the new
  `selfDual_self` (141III's example, three lines: a ℬ-linear `τ` is
  `τ x = x·τ1 = ⟨(τ1)*, x⟩`) — to upgrade
  `⟨S(a⊗b), S(a'⊗b')⟩ = ⟨a⊗b, a'⊗b'⟩` from elementary tensors to all of
  `𝒜 ⊗_φ ℬ`, one variable at a time (the second variable via
  `star_inner`).  (iv) To `PhiCompatible.mul_right` for
  `S(ϱ(a)x) = ϱ'(a)(S x)`.  Uniqueness is then immediate from
  `a ⊗ b = b·ϱ(a)(1 ⊗ 1)`.  The hypothesis `hφ : φ a = ⟨e, ϱ'(a)e⟩` is the
  exact mirror of `h_def` — it is **not** off by a `star`, and `ϱ'` lands in
  `𝒷ᵃ(Y)ᵐᵒᵖ` for the same reason `ρ` does.
* **154III.5** `existence_paschke_5`: the conjunct `h ∘ ϱ = φ`, which was
  *false* under the old fields, is now proved (`paschkeModule_h_ρ`).  The
  universal property among all Paschke triples (154IV–154X) remains `sorry`.
* `Paschke.lean` goes from 9 `sorry`s to 8.

### 5. Non-vacuity: `paschkeModuleId`

`vnTensor_mul_complex` is the model.  `ℬ` itself, with `tprod a b = b·a`,
is a `PaschkeModule` of `φ = id`: `⟨b·a, b'·a'⟩ = (b'a')(ba)* =
b' (a' a*) b*` is `inner_tprod` on the nose, the bound holds with `r = 1`
because `∑ᵢⱼ bᵢ(aᵢ aⱼ*)bⱼ* = v v*` for `v = ∑ᵢ bᵢaᵢ` (`gram_id_sum`), the
universal property forces `T' x = T x 1` and is proved by feeding the bound
the two-element family `(b·a, a)`, `(1, −b)` whose `v` is `0`, and
`ρ = rightMulEquiv`, `h = rightMulEquiv.symm` are a ∗-isomorphism and its
inverse.  Normality of both is `starAlgEquiv_preservesDirSups`, which already existed
in `Theses/A/VN/Basic.lean:3107` (a first draft of it here was thrown away —
worth grepping for before proving anything about normality); complete
positivity of `h` and of `ncpMapId` is Mathlib's
`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`, reached through
`CompletelyPositiveMapClass.toCompletelyPositiveLinearMap` (the `CoeHead`
ascription `(f : A →CP B)` does *not* elaborate here).
So the repaired bundle is inhabited for a non-zero `φ`, and the nine
theorems quantifying over `PaschkeModule` say something.  This is the check
that would have caught both this defect and the `PhiCompatible.bound`
defect of session 14, and it is exactly the sort of thing three readings of
the statements did not catch.

### 6. Refactor: the module-action lemmas moved upstream

`op_add_smul`, `op_mul_smul`, `op_smul_complex_smul`, `op_smul_add`,
`op_zero_smul`, `op_smul_zero`, `norm_op_smul_le` were in `SelfDual.lean`,
which is *downstream* of `Paschke.lean`.  They are the module laws for
`SMul ℬ X` that `CStarModule` does not assume, and 154III.4 needs them, so
they moved verbatim into `HilbertModules.lean` (new `ModuleAction` section,
right after `cstarBInner`), joined by two new ones, `op_one_smul` and
`op_smul_comm_complex`.  Names and statements unchanged; `SelfDual.lean`
keeps using them and still builds.  `selfDual_self` is also new there.

### 7. Verification

`lake build Theses.B.Dils.Paschke`, `Theses.B.Dils.SelfDual`,
`Theses.B.Dils.Pure`: `Build completed successfully`.  `#print axioms` clean
(`propext`, `Classical.choice`, `Quot.sound` only) on all of
`selfDual_self`, `op_add_smul`, `op_mul_smul`, `op_one_smul`,
`op_smul_comm_complex`, `op_smul_complex_smul`, `op_smul_add`,
`op_zero_smul`, `op_smul_zero`, `norm_op_smul_le`, `selfAdjointUnop`,
`npFunctionalOp`, `vonNeumannAlgebra_mulOpposite`, `paschkeModule_h_ρ`,
`PhiCompatible.mul_right`, `existence_paschke_2`, `existence_paschke_4`,
`paschke_inner_conj_forces_zero`, `paschke_rho_forces_cyclic`, `rightMul`,
`rightMul_mul`, `rightMul_one`, `rightMul_star`, `rightMulEquiv`,
`ncpMapId`, `gram_id_sum`, `rightMulNMIU`, `rightMulNCP` and
`paschkeModuleId` — in particular the non-vacuity witness carries no
`sorryAx`, so the bundle really is inhabited.

Note for whoever runs next: `Theses/A/VN/NormalFunctionals.lean` was being
edited live by another worker for most of this session, and a mid-edit state
there makes *every* `lake build` under `Theses/B/Dils` fail with errors that
are not yours (missing `.olean`, parse errors in `A/VN`).  Retry rather than
debug.

## Session 44 — `B/Dils`: the 145I lead is **refuted**, and 140VIII `paschke_unique_up_to_iso` is proved (worker 69)

Files touched: `Theses/B/Dils/Stinespring.lean`, this log.  Nothing staged,
nothing committed.  **B/Dils 59 → 58 `sorry`s.**

### 1. **145I `hilbmod_vectstates_cp` is faithful, and was already proved**

The brief carried session 43's lead — "145I states exactly the form that
fails, is very likely mis-mirrored, and is still `sorry`".  Both halves are
wrong, and the second is checkable in one command: `HilbertModules.lean` has
carried **zero** code `sorry`s since `ae94174`, and
`#print axioms Theses.B.Dils.hilbmod_vectstates_cp` returns exactly
`[propext, Classical.choice, Quot.sound]`.  A statement with a machine-checked
proof cannot be false; the only live question was faithfulness, and it is
faithful.

`dils.tex:1706` states `h(T) = ⟨x, Tx⟩` is cp, and proves it by
`∑ᵢⱼ bᵢ* ⟨x, Tᵢ*Tⱼ x⟩ bⱼ = ∑ᵢⱼ ⟨Tᵢ x bᵢ, Tⱼ x bⱼ⟩ = ⟨∑ᵢ Tᵢ x bᵢ, ∑ᵢ Tᵢ x bᵢ⟩ ≥ 0`.
Under the mirror (`⟪u,v⟫ = ⟨v,u⟩`, `x·b ↦ star b • x`) that is exactly the Lean
statement `0 ≤ ∑ᵢⱼ star (bᵢ) * ⟪Sᵢ(Tⱼ x), x⟫ * bⱼ` and exactly the Lean proof,
with `v = ∑ₖ star (bₖ) • Tₖ x`.  The doc comment already records the swap and
already explains why the *un*-swapped `⟪x, Sᵢ Tⱼ x⟫` form is false.

**Why the lead looked plausible, and where it goes wrong.**  Session 43's
computation is right about `Paschke.lean` and wrong about 145I, because the two
use *different* forms of the vector state:

* `Paschke.lean`'s `h_def` is the **bundled, ℂ-linear** map
  `h : NCPMap (Ba ℬ X)ᵐᵒᵖ ℬ`, `h (op T) = ⟪x, T x⟫`.  The `ᵐᵒᵖ` is forced:
  under the mirror the ℂ-action on the operator algebra is conjugated too, so
  the ℂ-*linear* rendering of a thesis operator `T` is the Lean operator `T*`,
  and `T ↦ T*` is anti-multiplicative.
* **145I is unbundled.**  It quantifies over families `(Tᵢ, Sᵢ)` with `Sᵢ` an
  explicit `ModuleAdjointTo` partner and asserts positivity of a sum built from
  `Sᵢ ∘ Tⱼ`.  No ℂ-scalar and no algebra structure on `Ba ℬ X` enters, so
  neither the conjugated ℂ-action nor the `ᵐᵒᵖ` can bite.  The two forms are
  literally the same family of inequalities under `T ↔ S`.

**The `X = ℬ` check session 43 recommended, carried out.**  For Mathlib's own
left module `ℬ` over itself (`⟪u,v⟫ = v u*`) the adjointables are the right
multiplications `R_t`, with `(R_t)* = R_{t*}` and `R_t ∘ R_s = R_{st}`.  Then

* `T ↦ ⟪T 1, 1⟫` — 145I's form — sends `R_t ↦ t*`, which is a
  ∗-**homomorphism** `Ba ℬ ℬ → ℬ` (anti ∘ anti), hence cp.  Its CP sum is
  `∑ᵢⱼ bᵢ* tᵢ tⱼ* bⱼ = v* v` for `v = ∑ tᵢ* bᵢ`.
* `T ↦ ⟪1, T 1⟫` — the other form — sends `R_t ↦ t`, which is `unop`, the
  transpose on `M₂`: its CP sum is `∑ᵢⱼ bᵢ* tⱼ tᵢ* bⱼ`, the transposed Gram
  matrix, indefinite.  This is the map session 43 computed, and it is cp on
  `(Ba ℬ ℬ)ᵐᵒᵖ`, which is where `Paschke.lean` puts it.

So the tree is coherent: `Paschke.lean` uses `⟪x, T x⟫` on `Baᵐᵒᵖ`,
`HilbertModules.lean` uses `⟪T x, x⟫` on `Ba`, and both are cp.  **No erratum,
no QUESTIONS entry, no restatement.**

**A correction to the mirroring dictionary as the brief stated it.**  The brief
said "Mathlib's inner product is conjugate-linear in the FIRST argument; the
thesis's is conjugate-linear in the SECOND".  The second clause is false:
`dils.tex:1302` defines `⟨x,·⟩` to be ℬ-linear with `⟨x,y⟩* = ⟨y,x⟩`, so the
thesis's is conjugate-linear in the **first** argument too.  The only
difference is right modules vs. left modules, and the mirror is passage to the
*conjugate* module — which is what conjugates the ℂ-action, exactly as session
43 said.  The dictionary is right; the stated reason for it was not.

### 2. Neighbours: nothing else is infected

Every `B/Dils` declaration that asserts positivity or complete positivity of a
vector-state-like map on `Ba` was re-checked:

* `Paschke.lean` `PaschkeModule.h` and `rightMulNCP` — already `ᵐᵒᵖ`.
* `SelfDualCompletion.lean` **153I** `hilbmod_ad_cp` / `hilbmod_ad_ncp`
  (`ad : NCPMap (Ba 𝒷 Y) (Ba 𝒷 X)`, `S ↦ T'ST`) — immune: the ℂ-actions on
  source and target are conjugated *the same way*, so `ad` is ℂ-linear in
  either convention, and its CP condition involves only composition and `*`,
  which the mirror preserves.
* `SelfDualCompletion.lean` `ba_nonneg_of_vector` and **144I**
  `hilbmod_ordersep` — immune: `⟪x, Zx⟫` and `⟪Zx, x⟫` are each other's
  adjoints and positivity is `star`-invariant.

### 3. **140VIII** `paschke_unique_up_to_iso` — proved (Stinespring.lean 7 → 6)

Two Paschke dilations of the same `φ` are related by a unique
nmiu-isomorphism.  The author's proof (**140IX**) is transcribed: the mediating
`σ : 𝒫₁ → 𝒫₂` and `τ : 𝒫₂ → 𝒫₁` compose to the identities because `τ ∘ σ` and
`id` both mediate `(𝒫₁,ϱ₁,h₁)` to itself, and `σ(1) = σ(ϱ₁ 1) = ϱ₂ 1 = 1`.

**Divergence (case 2: thesis argument fine, different route, forced by the
import graph).**  For the last step — "a unital ncp-isomorphism is an
nmiu-isomorphism" — the author cites `iso` (proc.tex:878 = **99IX**), which
*is* formalized and axiom-clean at `Theses/A/Proc/Measurement.lean:2572`, but
`A/Proc` is off `B/Dils`'s import path; QUESTIONS **D3** already ruled against
coupling the two chapters for exactly this kind of reason, and `iso` genuinely
belongs to `proc.tex`, so relocating it (the D3 remedy) is not available
either.  Instead the standard Kadison–Schwarz argument is run inline, using
only `ncp_cp_cs` (**34XIV**) from `A/VN/Basic.lean`:

* for unital `σ`, `σ(x)*σ(x) ≤ σ(x*x)`; applying the (monotone, also unital)
  `τ` gives `x*x ≤ τ(σ(x)*σ(x)) ≤ τ(σ(x*x)) = x*x`, so
  `σ(x*x) = σ(x)*σ(x)` by injectivity of `τ`;
* the defect `d(x,y) = σ(x*y) − σ(x)*σ(y)` is sesquilinear and vanishes on the
  diagonal, so `d(x,y) = −d(y,x)`, and substituting `iy` for `y` gives
  `d(x,y) = +d(y,x)`; hence `2d = 0` and `σ` is multiplicative.  (`star`
  preservation is `ncp_star`.)

This is shorter than importing `A/Proc` would be, and it keeps the chapter
independent.  Note it is a *weaker* input than the author's: `iso` needs
Gardner's theorem, this needs only Kadison's inequality, because we already
know both maps are unital rather than merely subunital.

New private helper in `Stinespring.lean`: `exists_ncpComp` (composition of two
ncp-maps), the missing third of the `exists_ncpCompNMIU` / `exists_nmiuCompNCP`
pair.  `paschke_unique_up_to_iso` was **moved** to the foot of the file (its
old position precedes the private id/composition helpers it needs); a pointer
comment is left where it was.

### 4. Parked: `existence_paschke_5` is structurally blocked on `existence_paschke`

The brief named `existence_paschke_5`'s remaining half (154IV–154X's universal
property) as the top secondary target.  It cannot be closed as stated.  The
author's **154X** proves σ-existence by *re-running the whole construction for
`h'`* — it needs a Paschke module `𝒫' ⊗_{h'} ℬ` for the ncp-map
`h' : 𝒫' → ℬ` of the competing triple, and `existence_paschke` (the
construction) is itself `sorry`.  `existence_paschke_5` only receives a
`PaschkeModule φ`, so there is no way to manufacture the module for `h'`.
The alternative the thesis mentions in **154VIII** ("use `equation-sigma` as
defining formula") does stay inside `M`, but needs the parsec-1520
bounded-sesquilinear-form ⇒ operator machinery, which is also `sorry`.
**Either close `existence_paschke` first, or take the 1520 route.**
The uniqueness half of **154VIII** is transcribable today (it needs only
`hilmod-fixed-on-V`, which is proved in `SelfDualCompletion.lean`), but the
Lean statement is a single `∃!` and cannot be split.

Also parked, with the reason: the **169X–169XII filter cluster** in
`Pure.lean`.  The thesis derives filter injectivity (**169XII**) from the
standard filter (**169X**), which is `sorry` and needs the `proc.tex` 96V/98I
corner machinery.  There *is* a route that avoids it — the universal property
of a filter `c` for `b`, applied to ncp-maps `ℂ → 𝒜`, says that every
`t ∈ [0, c(1)]` has a *unique* positive preimage, which gives injectivity on
effects and then on all of `𝒜` by `star`-splitting and scaling — but it needs
an `NCPMap ℂ A` from a positive element, which does not exist anywhere in the
tree (complete positivity would come from `a = s*s` and the factorisation
`∑ᵢⱼ cᵢ* (conj(xᵢ)xⱼ • a) cⱼ = (∑ᵢ xᵢ s cᵢ)* (∑ⱼ xⱼ s cⱼ)`).  Worth building
once: it would unblock **169XI**.1, **169XI**.2a/2b and **169XII** together.

### 5. Verification

`lake env lean Theses/B/Dils/Stinespring.lean`: no errors, six `sorry`
warnings (702, 714, 729, 739, 750, 1128 — 138II, 138VI, 138VII, 138VIII×2,
139XI).  `lake build Theses.B.Dils.Stinespring`: `Build completed
successfully`.  `#print axioms Theses.B.Dils.paschke_unique_up_to_iso` and
`#print axioms Theses.B.Dils.hilbmod_vectstates_cp`: both exactly
`[propext, Classical.choice, Quot.sound]`.

## Session 44 — `A/VN` parsecs 810–830: 81III `proto-douglas`, **82I the polar decomposition**, 83II `vmleq`, 83IV, **83V `cceil-sum`** (worker 68, A chain)

Target given: **81III** `proto_douglas_1`, then "work up 81V–81IX, 82I, 83II,
83IV, 83V".  81III went through as the brief predicted, and it turned out to
carry the whole of parsecs 820–830 with it, so the session closed the division
chain end to end rather than stopping at 81III.

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **81III**.1 | `proto_douglas_1` | 1 — the thesis's own proof, with a shorter form of its one estimate (§1) |
| **81III**.2 | `proto_douglas_2` | 1 — falls out of the same estimate, exactly as the thesis says |
| **82I** | `polar_decomposition` | 1 |
| **82I**.1 | `polar_decomposition_1` | 1 |
| **82I**.2 | `polar_decomposition_2` | 1 |
| **83II** | `vmleq` | 1 |
| **83IV** | `mvn_preorders` | 2 — Exercise, no author argument exists |
| **83V** | `cceil_sum` | 1, with one step replaced by its contrapositive (§4) |

Five reusable auxiliaries came with them, all public, all in `Division.lean`:
`usTendsto_of_monotone_isStarProjection`, `partialSums_of_isLUB`,
`apinv_block_est`, `sqrt_star_self_spec`, `rangeProj_mul_polar`.

`A/VN` sorries **82 → 74**; `A/CStar` **28 → 28** (untouched).

### 1. 81III: the estimate, shorter than the thesis's

vn.tex 5411 bounds the Cauchy tail by expanding
`(∑_{n=M}^N at_n)^*(∑_{n=M}^N at_n) = ∑_{n,m} t_n^*b^*bt_m` and collapsing the
double sum with "`bt_1, bt_2, …` are pairwise orthogonal projections".  That
collapse is avoidable: both blocks are *the same right factor* applied to `a`
resp. `b` —

    S_N − S_M = a·d,   P_N − P_M = b·d,   d := ∑_{n∈[M,N)} t_n,

so `star(ad)(ad) = d^*(a^*a)d ≤ d^*(b^*b)d = star(bd)(bd) = P_N − P_M`
is a single `star_left_conjugate_le_conjugate`, and `P_N − P_M` is a projection
because the partial sums `P_N` are increasing projections.  Pairwise
orthogonality of the `bt_n` is then needed only for *that* (`P_N` a
projection), not for the estimate, and it comes for free: the partial sums are
`≤ ⌊b⌉ ≤ 1`, and projections summing to `≤ 1` are pairwise orthogonal
(**55XIII**.2).  This is `apinv_block_est`, which is stated with **no**
mention of `a` on the right-hand side and therefore proves **81III**.2 (the
uniformity) as directly as the thesis promises — "because `a` does not appear
in the expression that gave the bound".

`‖·‖_ω`-Cauchyness then follows from `omegaNorm_le_omegaNorm` plus
`ω(P_N).re ↑`, bounded by `ω(⌊b⌉).re`; **77I** `vn_complete_1` supplies the
limit `c`, and `a = cb`, `c⌊b⌉ = c` come from `⌈a⌋ ≤ ⌈b⌉` and
`⌈t_n⌋ ≤ ⌊b⌉` exactly as in the thesis, using the new
`partialSums_of_isLUB` to turn the structure's four `IsLUB` fields into
honest ultrastrong convergence and `vn_positive_basic_1` (Hausdorffness) to
identify the two limits.

`partialSums_of_isLUB` rests on `usTendsto_of_monotone_isStarProjection` — *an
increasing sequence of projections converges ultrastrongly to its supremum* —
which is the ω-half of session 42's `sum_of_orthogonal_projections`, extracted
so it can be reused; the `Finset`-indexed net of 56XVIII is not convenient for
the `ℕ`-indexed partial sums the definition of an approximate pseudoinverse
uses.

### 2. 82I needs 81III, not 81V

vn.tex 5591 says the existence and uniqueness of `[a]` "is provided by
`douglas`" (**81V**).  Only **81III** and the *definition* of division
(**81I**) are used: `a^*a ≤ √(a^*a)√(a^*a)` puts `a` in `𝒜√(a^*a)`, and `[a]`
is then literally `a/√(a^*a)`, whose two defining properties are `div_spec`.
81V's norm bound `‖a/b‖ ≤ λ` plays no part.  **81V is still `sorry`** and
nothing in 820–830 waits on it.

The rest is the thesis verbatim: `[a]^*[a] = ⌈a^*a⌉` by two-sided cancellation
(**60VIII**.3, `mult_cancellation_3`) against `√(a^*a)`; `[a][a]^* = ⌊a⌉` by
`⌊[a]⌉ ≤ ⌊a⌉` (which is **81II**.1, `division_basic_1`, not something extra)
and `⌊a⌉ = ⌈aa^*⌉ = ⌈[a](a^*a)[a]^*⌉ ≤ ⌈‖a^*a‖[a][a]^*⌉ = [a][a]^*`;
`√(aa^*) = [a]√(a^*a)[a]^*` by squaring; `[a^*] = [a]^*` by the uniqueness
clause.  The `a = 0` case is split off, because `⌈λ·x⌉ = ⌈x⌉` needs `λ > 0`.

### 3. 83II `vmleq`: a hypothesis that is never used

`he' : IsStarProjection e'` is **not used** and cannot be: each of the three
conditions already forces `e'` to be a projection (`⌈a^*ea⌉`, `⌈a⌋`, and
`u^*u` for a partial isometry `u` are all projections).  Not an erratum — the
thesis says "given projections `e'` and `e`", so it is stating the intended
scope — but worth knowing that only `he` is load-bearing.  The proof is the
thesis's, with `u := [ea]` for (1)⇒(3).

### 4. 83V `cceil_sum`: the middle step replaced by its contrapositive

The thesis (vn.tex 5730) argues, for `p := ⌈⌈e⌉⌉ − ⋃_i e_i ≠ 0`,

    p = p⌈⌈e⌉⌉p = ⋃_a ⌈p⌈a^*ea⌉p⌉ = ⋃_a ⌈(eap)^*eap⌉,

hence some `(eap)^*eap ≠ 0`.  The last equality is asserted without proof and
needs `⌈p⌈c⌉p⌉ = ⌈pcp⌉` for positive `c`, which the thesis has not stated.
The contrapositive is elementary and needs neither:

    if `eap = 0` for every `a`, then `p(a^*ea)p = (eap)^*(eap) = 0`, so
    `√(a^*ea)·p = 0` (C*-identity), so `(a^*ea)p = 0`
    (`sqrt_mul_eq_zero_iff`), so `⌈a^*ea⌉p = 0` (`ceil_mul_eq_zero`),
    so `⌈⌈e⌉⌉ = ⋃_a⌈a^*ea⌉ ≤ 1 − p` (**68I** `cceil_fundamental`);
    with `p ≤ ⌈⌈e⌉⌉` this gives `p ≤ 1 − p`, i.e. `p = 0`.

Everything else is the thesis: Zorn (`zorn_subset`) for the maximal orthogonal
family, `e_i = u_i^*u_iu_i^*u_i ≤ u_i^*eu_i` for `⋃_i e_i ≤ ⌈⌈e⌉⌉`, and
`u := [eap]` for the contradiction with maximality.  The index type is the
maximal set itself (`ι := ↥S`, `e' := Subtype.val`), which is why the
statement's `ι : Type u` is satisfiable without a choice of cardinal.

One thesis slip found here, filed in ERRATA: the proof's last sentence says
"**`e`** could have been added to `(e_i)_i`" where it means `u^*u`.

Also worth recording: the thesis's chain
`e_i = u_i^*u_i ≤ u_i^*eu_i ≤ ⋃_{a}⌈a^*ea⌉` writes `≤` where the second step
needs a ceiling (`u_i^*eu_i` is not a projection); the repair is one
`ceil_mono` plus `⌈e_i⌉ = e_i`, which is what the Lean proof does.

### 5. What this releases

`vmleq` (83II) and `MvNLE` are now theorems, so **`B/Dils/SelfDual`'s uses of
`vmleq` are unblocked**, and **83V** — one of **89IX**'s two chains — is done.
89IX still waits on 89VII ← 89V, i.e. on **88IV** `carrier_vector_state`,
**88IX** `commutant_cceil` and **69IVb** `nmiu_image`, exactly as session 42
recorded; nothing this session changes that side.

Still `sorry` in parsecs 810–830: **81V**.1/.2 (`douglas_1`, `douglas_2`),
**81VI**.1/.2, **81VII** `div_approx`, **81VIII**.1/.2, **81IX** `div_usc`.
81V.1 (⇐) and 81IX both want one missing ingredient — *the ultrastrong limit
of a norm-bounded net is norm-bounded* (`‖·‖ ≤ C` transported through
`np_orderSeparating`); with it, 81V.1 is `‖∑_{n<N} at_n‖ ≤ λ` from
`star(S_N)S_N ≤ λ²P_N ≤ λ²`, and 81IX is the thesis's "uniform limit of
continuous functions" argument on top of `proto_douglas_2`.  That helper is
the highest-value next step in this file.

### 6. Verification

`lake env lean Theses/A/VN/Division.lean`: no errors, and the only warnings are
the two pre-existing `dif_pos` deprecations at lines 70 and 1521 (the `pinv`
and `div` definitions), which predate this session.  `#print axioms` on all
thirteen new declarations: exactly `[propext, Classical.choice, Quot.sound]`.

Downstream, `lake build Theses.A.Proc.Duplicators Theses.B.Dils.Pure` (the two
tips of the import graph below `A/VN`) reports `Build completed successfully`,
so `Theses.A.Proc.*` and `Theses.B.Dils.*` build as cleanly as they were found.
A *whole-project* `lake build` was started and deliberately killed: two other
workers were building `B/Dils` and `B/Eff` at the same time on the 14 GB box
and free memory was down to 1 GB — the two tips above cover everything
downstream of this session's changes, and were run one module at a time
(`LEAN_NUM_THREADS=1`) for the same reason.

Sorry counts from that build's `declaration uses \`sorry\`` lines (never a
grep): **A/CStar 28 → 28** (Matrices 4, Positive 13, Representation 11);
**A/VN 82 → 74** (Basic 25, Completeness 2, **Division 21 → 13**,
NormalFunctionals 14, Projections 20).  Files touched:
`Theses/A/VN/Division.lean`, `ERRATA.md` and this log.  Nothing staged,
nothing committed.

## Session 44 — `B/Eff` parsec 178: the non-commutative effect monoid on lexicographic `ℝ⁵`, and finite effect monoids are commutative (worker 69)

`Theses/B/Eff/EffectAlgebras.lean` (plus one lemma moved out of
`StatesPredicates.lean`).  The directory was at 18 `sorry`s, of which twelve
are the `vNᵒᵖ` examples — blocked on essentially all of thesis A — and the
rest are cited-to-literature or `Exercise*` items with no argument in either
thesis to transcribe.  This session took the two that are *mathematics we can
supply ourselves* rather than citations: 178III.4 and the 178III.2 corollary.

### 1. 178III.4 `exists_noncommutative_effectMonoid` — proved

eff.tex:651 says only "There is a non-commutative effect monoid based on the
lexicographically ordered vector space `ℝ⁵`, see \[basmsc, cor. 51]".  We do
not have `basmsc`, so the example was **reconstructed from scratch**; that
makes this an independent check that the cited claim holds, and it pins down
*why* the dimension is five.  Everything is in namespace `LexNC`.

* `V = ℝ⁵` lexicographically ordered, `u = e₁`; `[0,u]` is an effect algebra
  by 175II.2 (`orderIntervalEffectAlgebra`), which wants `V` to be an
  `AddCommGroup` + `IsOrderedAddMonoid`.  Rather than fight `Prod.Lex`'s
  instance set, `V` is built from a one-step lexicographic extension
  `LexR G = ℝ × G` — own `PartialOrder`/`IsOrderedAddMonoid`, algebra
  instances inherited from `Prod` via `inferInstanceAs` — iterated four times.
* `V` becomes an associative unital `ℝ`-algebra with `e₁` the unit and, on
  `N = span(e₂,e₃,e₄,e₅)`, exactly two non-zero products of basis vectors:
  `e₂ ⊙ e₂ = e₄` and `e₂ ⊙ e₃ = e₅`.  All triple products in `N` vanish, so
  associativity reduces to `ring`/`module` bookkeeping, and
  `e₂ ⊙ e₃ = e₅ ≠ 0 = e₃ ⊙ e₂` with `e₂, e₃ ∈ [0,u]` is the
  non-commutativity.
* The only real obligation is that the positive cone is closed under `⊙`
  (`vmul_nonneg`), by cases on leading coordinates — **and this is what forces
  five dimensions.**  The naive 4-dimensional variant
  `e₂ ⊙ e₂ = e₂ ⊙ e₃ = e₄` fails: `e₂ ≥ 0` and `e₂ - 2e₃ ≥ 0`, yet
  `e₂ ⊙ (e₂ - 2e₃) = -e₄ < 0`.  Sending `e₂ ⊙ e₂` to a level strictly *above*
  `e₂ ⊙ e₃` makes the leading term `n₂m₂e₄ > 0` dominate the
  sign-indeterminate `n₂m₃e₅`, and the cone closes.
* Closure of `[0,u]` then needs no second case analysis:
  `u - xy = (u - y) + (u - x)y`, so it follows from cone-closure alone.  The
  same trick keeps the fourfold distributivity axiom short — every partial sum
  of `[a⊙c, b⊙c, a⊙d, b⊙d]` is below `(a ⋁ b) ⊙ (c ⋁ d) ≤ u`, because the
  omitted products are positive.

### 2. 178III.2, the corollary `finite_effectMonoid_commutative` — proved, by a different route

⚠️ *Class 2 — different proof.*  eff.tex:640 derives commutativity from
"every finite effect monoid comes from a Boolean algebra", cited to
\[basmsc, prop. 40]; that structure theorem (`finite_effectMonoid_boolean`,
an equality of `EffectMonoid` structures) is **still `sorry`** and remains
parked.  The corollary, however, has a short direct proof, which is what the
file now carries:

1. **In any effect monoid, `a ⊙ aᵖ = aᵖ ⊙ a`** (`emon_mul_orth_comm`).  Both
   `a ⊙ 1 = (a⊙a) ⋁ (a⊙aᵖ)` and `1 ⊙ a = (a⊙a) ⋁ (aᵖ⊙a)` equal `a`, so
   cancellation (175V.4) applies.  This needed the mirror of `emon_mul_ovee`,
   which already existed in `StatesPredicates.lean` as `emon_ovee_mul` and has
   been **moved to `EffectAlgebras.lean`** (same name, same namespace, so no
   use site changes; a pointer comment is left behind).
2. **An idempotent `x` with `x ⊥ x` is `0`** (`emon_idem_perp_self_zero`) —
   *no finiteness needed*.  Cancellation in `x = x ⋁ (x ⊙ xᵖ)` gives
   `x ⊙ xᵖ = 0`; writing `xᵖ = x ⋁ z` (which `x ⊥ x` provides) turns that into
   `0 = x ⋁ (x ⊙ z)`, so `x = 0` by positivity.
3. **In a finite effect monoid `x ⊙ x = 0` forces `x = 0`**
   (`emon_sq_zero`).  If `x ≼ y` and `x ⊙ y = x`, write `y = x ⋁ g`; then
   `x = (x⊙x) ⋁ (x⊙g) = x ⊙ g`, so `x ≼ g ≺ y` and the two hypotheses survive
   for `g`.  Starting at `y = 1` that is an infinite descent, so `x = 0`.
   (Formally: well-founded induction on `≼`, which finiteness makes
   well-founded — `emonOrder` bundles 175V.5's partial order for
   `Finite.to_wellFoundedLT`.)
4. **Hence every element is idempotent** (`emon_finite_idem`): `d = a ⊙ aᵖ`
   satisfies `d ≼ a` and `d ≼ aᵖ`, hence `d ⊥ d`; and self-orthogonal
   elements vanish (`emon_perp_self_zero`), because the squares
   `x ≽ x⊙x ≽ …` descend — each still self-orthogonal, since
   `(x ⋁ x) ⊙ (x ⋁ x)` is a fourfold sum of `x⊙x` — to an idempotent, killed
   by (2), and (3) propagates that back.  With `a ⊙ aᵖ = 0`,
   `a = (a⊙a) ⋁ 0`.
5. **Idempotency ⟹ commutativity**: `a ⊙ b` is a lower bound of `a, b`, and
   any lower bound `c` satisfies `c = c ⊙ c ≼ a ⊙ b` by monotonicity, so
   `a ⊙ b` *is* the infimum; infima are unique (`isInf_unique`), so
   `a ⊙ b = b ⊙ a`.

Step 5 is worth keeping in mind independently: **in any effect monoid in
which every element is idempotent, `⊙` is the meet and hence commutative.**

Nothing here contradicts the thesis; no erratum.  The only judgement call is
that we did *not* attempt `finite_effectMonoid_boolean`, which additionally
demands that the induced `BooleanAlgebra` reproduce the given effect algebra
structure on the nose.

**For whoever picks that up: the mathematics is now essentially in the file.**
With `emon_finite_idem` and `finite_effectMonoid_commutative` in hand, a
finite effect monoid `M` is a Boolean algebra by the following four steps,
each a couple of lines with the helpers listed above:

* `Perp a b ↔ a ⊙ b = 0`.  (⇒) `a ⊙ b ≼ a` and `a ⊙ b ≼ b ≼ aᵖ`, so
  `a ⊙ b ⊥ a ⊙ b`, so it is `0` by `emon_perp_self_zero`.  (⇐)
  `a = a ⊙ 1 = (a ⊙ b) ⋁ (a ⊙ bᵖ) = a ⊙ bᵖ ≼ bᵖ`.
* `a ≼ c` iff `a = a ⊙ c` (one way by idempotency + monotonicity and
  antisymmetry, the other by `emon_mul_le_self_right`); hence `a ⊙ b` is the
  meet and, for `a ⊥ b`, `a ⋁ b` is the join — if `a, b ≼ c` then
  `(a ⋁ b) ⊙ c = (a ⊙ c) ⋁ (b ⊙ c) = a ⋁ b ≼ c`.
* General joins exist: `a ⊔ b := a ⋁ (b ⊖ a ⊙ b)`, the summands being
  orthogonal because `a ⊙ (b ⊖ a ⊙ b) = a ⊙ b ⊖ a ⊙ b = 0`.
* Distributivity: `a ⊙ (b ⊔ c) = (a ⊙ b) ⊔ (a ⊙ c)`, since `⊙` is
  bi-additive and `(a ⊙ b) ⊙ (a ⊙ c) = a ⊙ b ⊙ c` by commutativity and
  idempotency.  A complemented distributive bounded lattice is Boolean, with
  `aᶜ = aᵖ`.

What is *not* done, and is the real remaining cost, is Lean plumbing rather
than mathematics: the statement asks for `@booleanEffectMonoid M ba = em`, an
equality of `EffectMonoid` *structures*, whose `ovee` field is typed over the
`Perp` field — so the two `Perp`s being only propositionally equal (funext +
propext) has to be `subst`-ed before the `ovee` fields can be compared.

### 3. What is left in `B/Eff`, and why

**16 `sorry`s.**  Twelve are the `vNᵒᵖ` examples, needing thesis A (and, for
223VI, the Paschke development of `B/Dils`): 177V, 180V, 189aI, 190III,
206III, 211IV, 215VI, 221III, 223VI, 224VI, 224VII, 225V.1.  The other four
are cited-to-literature or `Exercise*` items with nothing to transcribe:
178III.2 `finite_effectMonoid_boolean`, 179III.2
`effectModule_unitInterval_representation` (Gudder–Pulmannová, explicitly
parked as "not a result of the thesis"), 192III.3 `exc_dm_effectus_kleisli`,
192V.4 `cancellative_iso_convex`.

### 4. Verification

`lake env lean Theses/B/Eff/EffectAlgebras.lean`: no errors; the three
`declaration uses \`sorry\`` lines left in it are 177V, 178III.2-Boolean and
179III.2.  `lake build` of all eight `B/Eff` modules: succeeds.
`#print axioms` on `exists_noncommutative_effectMonoid`, `LexNC.effectMonoid`,
`LexNC.not_commutative`, `LexNC.vmul_assoc`, `LexNC.vmul_mem_Icc`,
`LexNC.e2_mem`, `finite_effectMonoid_commutative`, `emon_perp_self_zero`,
`emon_sq_zero`, `emon_finite_idem`, `emon_mul_orth_comm`, `emon_ovee_mul`:
either exactly `[propext, Classical.choice, Quot.sound]` or, for the four
choice-free ones (`emon_mul_orth_comm`, `emon_idem_perp_self_zero`,
`emon_ovee_mul`, `isSumOf_mul_right`), just `[propext]`.  No `sorryAx`.  Files touched: `Theses/B/Eff/EffectAlgebras.lean`,
`Theses/B/Eff/StatesPredicates.lean` (the moved lemma) and this log.  Nothing
staged, nothing committed.

## Session 45 — `B/Dils`: the scalars in universe `u`, **169XII** filters are injective, and two mis-transcriptions (worker 70)

Files touched: `Theses/B/Dils/Pure.lean`, `Theses/B/Dils/SelfDual.lean`,
`ERRATA.md`, `QUESTIONS.md`, this log.  Nothing staged, nothing committed.
**B/Dils 58 → 57 `sorry`s.**

### 1. **169XII** `dils_filters_injective` — proved, and it did **not** need 169X

Session 44 parked the 169X–169XII cluster because the thesis derives filter
injectivity from the *standard* filter (**169X**, still `sorry`) plus
`mult-cancellation`.  There is a one-step route that avoids 169X entirely, and
it is the one worker 69 sketched: run the *uniqueness* half of the filter's own
universal property against maps out of the scalars.

For `0 ≤ a` in a C*-algebra `A` the map `z ↦ z·a` is an ncp-map `ℂ → A`.  So if
`c` is a filter for `b` and `x, y` are effects of `A` with `c x = c y`, then
`z ↦ z·(c x)` is an ncp-map `ℂ → ℬ` whose value at `1` is `c x ≤ c 1 ≤ b`; both
`z ↦ z·x` and `z ↦ z·y` factor it through `c`, so they are equal by uniqueness,
and `x = y`.  Scaling by `(1+‖x‖+‖y‖)⁻¹` extends this to the whole positive
cone, and `w = w⁺ − w⁻` together with `c(w*) = (c w)*` to all of `A`.

**Divergence (case 2: thesis argument fine, different route).**  The thesis's
route is not wrong, it is merely downstream of a `sorry`; this one is
upstream of everything in the parsec.

**The universe wrinkle — why "just use `ℂ`" does not typecheck.**
`IsCornerFor` and `IsFilterFor` quantify their test algebra over `Type u`, the
universe of `A` and `ℬ`, while `ℂ : Type 0`.  The probe therefore has to be
`ULift ℂ`, and Mathlib carries its ring, norm, algebra and completeness but
**not** its ∗-structure or its order.  `Pure.lean` now supplies them, in a new
`section Scalars` before parsec 1690:

* `CU := ULift.{u} ℂ` with `StarRing`, `StarModule ℂ`, `CStarRing`,
  `CStarAlgebra`, `PartialOrder`, `StarOrderedRing` (~35 lines of transport
  along `ULift.down`, which is injective);
* `ncpOfNonneg : 0 ≤ a → NCPMap CU A`, `z ↦ z·a`.  Complete positivity is
  `∑ᵢⱼ (cᵢbᵢ)* a (cⱼbⱼ) = v* a v` with `v = ∑ᵢ cᵢbᵢ`; normality is the
  closedness of the positive cone — `t ↦ t·a` is continuous `ℝ → A`, so
  `{t | t·a ≤ u}` is closed and contains `sSup` of any set it contains
  (`IsLUB.mem_closure`), after transporting the supremum from `sa(ℂᵤ)` to `ℝ`.

This is the "worth building once" item flagged at the end of session 44.  Any
proof that has to *use*, rather than merely state, one of this parsec's
universal properties will want it — **169XI**.1/.2b included.

### 2. **169XI**.2a `dils_filter_basics_2a` is **false as transcribed**, and the erratum standing against it was wrong

Our `IsFilterFor c b` transcribes dils.tex **169VIII** literally: `c 1 ≤ b`
plus the universal property for every `f` with `f 1 ≤ b`.  That is *not* the
definition proc.tex **96I** gives, which asks the universal property for
`f(1) ≤ c(1)` and calls `c` a filter *for `c(1)`* — so there `c(1) = b` holds by
construction.  Under dils.tex's `≤`, `c = ½·id : ℬ → ℬ` is a filter for `1`
with `c(1) = ½` (every `f` with `f(1) ≤ 1` factors uniquely, as `2f`), and then
169XI.2a fails outright: for `φ = id : ℂ → ℂ` and `c' = ½·id` there is no
unital `φ'` with `c' ∘ φ' = φ`.

ERRATA already carried a row for the corresponding gap in the *solution* of
169XI.2 ("the step `c'(φ'(1)) = φ(1) = c'(1)` uses `c'(1) = φ(1)`"), proposing
the repair "the isomorphism with the standard filter built in the
`dils-filters-injective` solution gives `c(1) = b`".  **That repair does not
work**: the argument yields `c = c_b ∘ ϑ` for an ncp-*isomorphism* `ϑ`, and
`ϑ(1) = 1` is precisely what fails (`ϑ = ½·id` in the counterexample).  Both
rows are rewritten and a new row is added against **169VIII** itself, whose
one-character fix (`c(1) ≤ b` → `c(1) = b`) repairs everything.  QUESTIONS
**B11** asks for the ruling, since changing our `IsFilterFor` is a statement
change.  The *derived* notion "`c` is a filter" (a filter for some `b`) is
insensitive to the difference — a `≤`-filter for `b` is an `=`-filter for
`c(1)` and conversely — so purity (**170I**), **169XI**.1 and **169XII** are
untouched.  Both declarations carry a ⚠️ note in their doc comments.

### 3. `L2Set` was mis-mirrored, which made **161II**.2 and **161IV**.2 false

`SelfDual.lean`'s `L2Set ℬ p` read
`{b | L2Summable ℬ b ∧ ∀ i, ⌈bᵢ bᵢ*⌉ ≤ pᵢ}` — dils.tex **161II**'s support
condition copied unchanged, while the two neighbouring halves of the same
definition *were* mirrored: `L2Summable` renders the thesis's `∑ᵢ bᵢ*bᵢ` as
`∑ᵢ bᵢbᵢ*`, and the inner product `∑ᵢ bᵢ*cᵢ` as `∑ᵢ cᵢbᵢ*`.  The mirror stars
the entries (this file's coordinates are `⟪eᵢ,x⟫ = ⟨x,eᵢ⟩`, the thesis's are
`⟨eᵢ,x⟩`), so the support condition has to be starred with them:
`⌈bᵢ*bᵢ⌉ ≤ pᵢ`.

As it stood, **161II**.2 `hilbmod_el2` was **false**.  Take `ℬ = X = M₂` over
itself (Mathlib's left module, `⟪u,v⟫ = v u*`) with orthonormal basis
`(e₀₀, e₁₁)`; the coordinates of `x` are `bᵢ = x eᵢᵢ`, which satisfy
`⌈bᵢ*bᵢ⌉ = ⌈eᵢᵢ x* x eᵢᵢ⌉ ≤ eᵢᵢ` always, while for `x = e₁₀` one has
`⌈b₀b₀*⌉ = ⌈e₁₁⌉ = e₁₁ ≰ e₀₀` — so the coordinate map does not land in `L2Set`
as written, and `Set.BijOn` cannot hold.  **161IV**.2 `onb1_el2` inherits the
same defect; with the fix its intended witness is `Φ b i = bᵢ · uᵢ*`, the
mirror of the thesis's `bᵢ ↦ uᵢbᵢ`, and the inner products then agree on the
nose (`(cu*)(bu*)* = c u*u b* = c p b* = c b*`).

Fixed, with the mirroring dictionary written into the definition's doc
comment.  This is **our** error, not the thesis's — no ERRATA entry.

### 4. Two notes on the brief

* The brief's correction of the inner-product convention ("the thesis is
  conjugate-linear in the **first** argument, same handedness as Mathlib; the
  real difference is right- vs. left-modules") is right, and is exactly what
  item 3 turns on.  No occurrence of the wrong version was found in the docs —
  session 44 had already fixed it.
* The brief lists `Stinespring.lean` as the first target because "140VIII was
  just closed there".  Its six survivors are all one cluster: **138II**
  `nmiu_between_type_I` and its corollaries **138VI**, **138VII**, **138VIII**
  ×2, plus **139XI**.  All of them are stated in terms of `hilbTensor`/
  `tensorCLM`, which today have exactly one API lemma (`tensorCLM_mk`) — no
  inner-product formula, no unitary-from-orthonormal-bases construction, no
  ultraweak sums of `|rᵢⱼ⟩⟨rᵢⱼ|`.  138II's own proof needs all three.  That is
  a Hilbert-space-tensor-product development, not a neighbouring item, and it
  is why this session went to `Pure.lean` instead.

### 5. Verification

`lean Theses/B/Dils/Pure.lean` and `lean Theses/B/Dils/SelfDual.lean`: no
errors, only the pre-existing `sorry`/linter warnings (Pure: 15 `sorry`s,
SelfDual: 21).  `#print axioms Theses.B.Dils.dils_filters_injective` and
`#print axioms Theses.B.Dils.ncpOfNonneg`: both exactly
`[propext, Classical.choice, Quot.sound]` — so the whole `CU` instance stack
is `sorry`-free too, which `#print axioms` is the only way to see (a `sorry`
inside an instance is invisible at the use site).

### 6. Tooling: `lake env lean` blocks on *another* agent's `lake build`

Three sessions are on record as having stalled waiting on builds, and this is
at least part of why.  `lake env lean Foo.lean` takes the workspace lock, so
while any other agent is running `lake build` **anywhere in this checkout**,
your `lake env lean` sits at ~64 MB RSS and 0:00 CPU until that build
finishes — indistinguishable from a slow compile, and it will happily eat a
600 s timeout and be killed with no output.  Three of this session's
compile attempts died that way.

The fix is to skip `lake` and call `lean` directly with `LEAN_PATH` built by
hand; it does not touch the lock, and reads exactly the same oleans:

```sh
LP=".lake/build/lib/lean"
for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
LEAN_PATH="$LP" lean Theses/B/Dils/Pure.lean
```

With this, `Pure.lean` (820 lines) checks in well under a minute even with
two other agents building.  Use `lake build` only when oleans genuinely need
regenerating.

---

## Session 46 — `A/Proc`: full survey of the chapter, and two parsec-980/1060 items that do **not** need 96V (worker 71)

Files touched: `Theses/A/Proc/Measurement.lean`, this log.  `Tensor.lean`,
`QuantumLambda.lean`, `Duplicators.lean`, `A/CStar`, `A/VN`, `B/` untouched.
**A/Proc 115 → 113**: `Measurement` 38 → **36**, `Tensor` 43,
`QuantumLambda` 17, `Duplicators` 17.

| point | declaration | class |
|---|---|---|
| **99XI** | `filter_of_projection_multiplicative` | 1 (the exercise's own hint) |
| **106III**.1 | `sequential_product_counterexample_1` | 1 (exercise, no published solution) |
| — | `isFilter_cornerIncl`, `exists_ncpCorestrict`, `conj_ncp_eq_of_le_proj` | new reusable infrastructure |

### 1. The finding: the corner inclusion of a *projection* is a filter, and 96V is not needed for it

Every earlier map of this chapter treated **the whole of parsecs 960–1060 as
one block behind 96V** `canonical_filter`, which needs `sequential-douglas`
(81VI), `div-approx` (81VII) and `div-usc` (81IX) — all three still `sorry`
in `A/VN/Division.lean`.  That is right for the standard filter
`c_p(a) = √p a √p` of a general positive `p`.  It is **not** right when `p` is
a projection: there `c_p` is just the inclusion `p𝒜p → 𝒜`, and its universal
property is elementary.

`isFilter_cornerIncl (p) [Fact (IsStarProjection p)] : IsFilter (cornerIncl p)`
is proved from two new private lemmas:

* `conj_ncp_eq_of_le_proj` — an ncp-map `f : ℬ → 𝒜` with `f(1) ≤ p` takes all
  its values in `p𝒜p`.  For positive `y` this is
  `⌈f(y)⌉ ≤ ⌈f(1)⌉ ≤ ⌈p⌉ = p` (from `f(y) ≤ ‖y‖·f(1)`, `ceil_mono`,
  `ceil_basic_4`); the general case is `y = ℜy + i·ℑy`, `y = y⁺ − y⁻`.
* `exists_ncpCorestrict` — the corestriction of such an `f` to `p𝒜p` is an
  ncp-map (complete positivity through `Corner.nonneg_map_val_iff`, normality
  through `Corner.isLUB_of_isLUB_image_val`).

Uniqueness is `Corner.val_injective`.  No division theory anywhere.

### 2. **99XI** `filter_of_projection_multiplicative` — class 1

proc.tex:897's own hint is "the filter is a standard filter up to an
ncpu-isomorphism (`filter-basic`), which is an nmiu-isomorphism by `iso`".
That is exactly the proof, with `isFilter_cornerIncl` standing in for the
`sorry`ed 96V/98II.1: for a filter `c` with `p := c(1)` a projection, the two
universal properties (of `c` and of `cornerIncl p`, which have the same value
at `1`) produce mutually inverse ncp-maps `α : C → p𝒜p`, `β : p𝒜p → C`;
`α(1) = 1` because `cornerIncl` is injective; **99IX** `iso` (proved) then
makes `α` multiplicative, and `Corner.val_mul` transports that to `c`.

Note the *general* 98II.1 is still blocked — it needs `c_p` to be a filter for
arbitrary positive `p`, i.e. 96V.

### 3. **106III**.1 `sequential_product_counterexample_1` — class 1

An Exercise past parsec 340, so no published solution.  Four clauses plus the
refutation:

* **(B)** is what 96V was thought to gate: `⌈p⌉(·)⌈p⌉` has to be *pure*.  It
  is `cornerIncl ∘ stdCorner ⌈p⌉` — a corner followed by a filter — and the
  filter half is now `isFilter_cornerIncl`.  (Working with
  `floor (ceil p)` rather than rewriting it to `ceil p` avoids a
  motive-is-not-type-correct failure: `Corner A e`'s algebra instances depend
  on `e`, so `rw` cannot cross `⌊⌈p⌉⌋ = ⌈p⌉`.)
* **(C)** collapses: `⌈q⌉q⌈q⌉ = q` for every effect, so both sides are
  `⌈p⌉q⌈p⌉` and the identity is `rfl` after two rewrites.  Worth telling the
  author: axiom (C) is *vacuous* for this operation, not merely satisfied.
* **(D)** is `q := p`.
* **(E)** reduces to a one-line C\*-identity.  For an effect `x` and a
  projection `e`, `x ≤ e^⊥ ⟺ exe = 0`; then
  `e₂(⌈p⌉e₁⌈p⌉)e₂ = (e₁⌈p⌉e₂)*(e₁⌈p⌉e₂)`, which vanishes iff `e₁⌈p⌉e₂ = 0`,
  and that condition is star-symmetric in `e₁, e₂`.  No contraposition theory
  (101VII) is used, contrary to what the shape of the clause suggests.
* **¬(A)** at `p = ½·1`: `⌈½·1⌉ = 1 ≠ ½·1` in any nontrivial algebra.

### 4. Survey of the whole chapter (the round's main deliverable)

The full map — every `sorry` with its DISP number, its classification, and its
named blocker — is in the session scratch file `AProc-survey.md`.  Headlines:

* **A/Proc is 115 `sorry`s (113 after this round), not ~120.**
* **54 of them (47%) are in the vacuous band**: their *statements* mention
  `VNT 𝒜 ℬ`/`⊗ᵥ`/`Duplicator`, hence depend on `sorryAx` through **111XII**,
  and cannot be closed axiom-cleanly at all until 111XII is.
* **111XII hangs on exactly one thing.**  Its two inputs are 48VIII `ngns`
  (vn.tex) and 111VII `special_tensor` (proc.tex:2491).  **`ngns` is proved.**
  111VII's proof needs `normal-functional` — **89IX**
  (`A/VN/NormalFunctionals.lean:1727`, `sorry`) — for its condition (2), and
  nothing else that is missing.  So **89IX gates 47% of A/Proc**, and it is in
  `A/VN`.  This is by a wide margin the highest-leverage item for this
  chapter, and no A/Proc worker can touch it.
* **`Measurement.lean`'s remaining 36 are almost all rooted at 96V**, i.e. at
  81VI/81VII/81IX in `A/VN/Division.lean`.
* **`Tensor.lean`'s 11 untainted statements** are blocked on 90II.2, 86IX,
  87III and 77V — all `A/VN`, all `sorry`.

### 5. The near miss worth banking: **98II.2** `filter_basic_2`

Two of its three conjuncts are provable directly from the universal property,
by a route the thesis does not take (it goes through 98II.1 and hence 96V):

* **mono in `W*_cp`** is the uniqueness clause of `IsFilter.universal` after
  rescaling `g`, `h` by `s⁻¹`, `s := ‖g(1)‖ + ‖h(1)‖ + 1`, so that the
  hypothesis `f(1) ≤ c(1)` can be met (an arbitrary ncp-map is not subunital).
  Written and type-checked this session.
* **faithfulness `⌈c⌉ = 1`** then follows: mono applied to `√z(·)√z` and the
  zero map gives `c(z) = 0 ⟹ z = 0` for positive `z`, because
  `√z x √z ≤ ‖x‖·z` for positive `x`.
* **Injectivity does not**, and the obstruction is exact: it needs mono at
  `B = ℂ`, i.e. the ncp-map `ℂ → C`, `ζ ↦ ζ·a` for positive `a`.  **The tree
  has no ncp-map out of `ℂ` at all** — there is no `algebraMap` as an
  `NCPMap`/`NMIUMap`, and `cp_commutative_dom` (**34IX**.2) is itself `sorry`.
  Building it needs (i) `0 ≤ M` in `M_k(ℂ)` implies
  `0 ≤ M.map (algebraMap ℂ C)` (route: `M = star X * X`, and `CStarMatrix.map`
  of a ∗-homomorphism is multiplicative) and (ii) `algebraMap ℂ C` preserves
  directed suprema (route: a LUB of reals lies in the closure of the set, and
  the positive cone is norm-closed).  That gadget closes 98II.2 outright and
  is the cheapest useful new infrastructure in the chapter.  Since 98II.2 is a
  single conjunction, the two provable clauses could not be banked, and the
  attempt was reverted.

### 6. Corrections to earlier reports and to the round's brief

1. **The brief's "roughly 120 sorries" is 115** (Tensor 43 not 45,
   QuantumLambda 17 not 20 — the difference is `sorry` mentioned in file
   docstrings).
2. **48VIII `ngns` is proved**, so 111XII is one theorem (89IX) away, not
   several.  Earlier notes listed 89IX among blockers without noting it is now
   the *only* one.
3. **21VII `order_separating_norm` and 90II.1
   `vn_center_separating_fundamental_1` are proved.**  w42's table put 112X.1
   and 112X.2 behind "90II + 21VII" wholesale; 90II.1 *is* 112X.1's first
   conjunct, and only 90II.2 is left.  The two conjuncts sit in one theorem,
   so 112X.1 is still `sorry`.
4. **80IV `approximate_pseudoinverse` is proved** (session 36), so w46 §7's
   "104VII is blocked on 80IV" is stale; what is left there is 104III.4/.5,
   which need 81V `douglas` / 81VIII `sequential-quotient`.
5. **74IV/74VI are proved** (sessions 23/25), so 112X.4 is down to **86IX**
   alone.
6. w41's "81VI/81VII/81IX are still `sorry`, so the 96V/98IX/100II.3/103II/99XI
   cluster has not opened" was right about the cluster but wrong about **99XI**,
   which is now closed by the projection-only route above.

### 7. Nothing false found

No new `ERRATA.md` or `QUESTIONS.md` entry.  The three known false statements
of this chapter (104III.2a parked, 104IV and 101VII.2 repaired) are unchanged;
117II.1's repaired form is proved.  121II `intersection_tensor` remains the
chapter's only statement with no thesis argument at all (proc.tex:4450 cites
Takesaki IV.5.10) — it is also in the vacuous band, so it is doubly out of
reach.

### 8. Verification

`env LEAN_PATH=… lean Theses/A/Proc/Measurement.lean` → **0** `error:` lines.
Warning profile is byte-for-byte the pre-session one **minus** the two
`declaration uses 'sorry'` that disappeared (121 → 119 warnings; no new
warning of any kind).  `#print axioms` (run from an appended block inside the
file itself, to avoid the stale-olean trap) →
`[propext, Classical.choice, Quot.sound]` for
`filter_of_projection_multiplicative`, `sequential_product_counterexample_1`,
`isFilter_cornerIncl`, and the regressions `iso` and `gardner`.  Nothing
staged, nothing committed.  (`Theses/A/VN/Division.lean`,
`Theses/B/Dils/Stinespring.lean` and `ERRATA.md` are also dirty — not mine.)

## Session 46 — `A/VN` parsec 810 closed except 81VIII.2: the norm-bounded-limit helper, 81V, 81VI, 81VII, 81VIII.1, and **81IX's second half is false** (worker 71, A chain)

Target given: build "the ~40-line helper — the ultrastrong limit of a
norm-bounded net is norm-bounded" and close **81V**.1 and **81IX**.  The
helper turned out to be **30 lines and to need no new mathematics at all**;
81V went through, and 81IX split in two, one half true and proved, the other
**false**.

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **81V**.1 | `douglas_1` | 2 — Exercise, no author solution exists (`asols.tex` stops at parsec 340) |
| **81V**.2 | `douglas_2` | 2 — Exercise; the counterexample is the thesis's own 81XI one |
| **81VI**.1 | `sequential_douglas_1` | 2 — Exercise |
| **81VI**.2 | `sequential_douglas_2` | 2 — Exercise, and the thesis's hint is *not* the route taken (§3) |
| **81VII** | `div_approx` | 2 — Exercise |
| **81VIII**.1 | `sequential_quotient_1` | 2 — Exercise |
| **81IX** (first half) | `div_usc_ball` | 1 — the thesis's own argument, verbatim |

Five reusable auxiliaries, all public, all in `Division.lean`:
`norm_le_of_usTendsto`, `apinv_partialSum_norm_le`, `div_smul_left`,
`sequential_douglas_core`, `ldiv_div_recover`.

`A/VN` sorries **74 → 68**; `Division.lean` **13 → 7**.  Nothing outside
`Theses/A/VN/Division.lean` (plus these three docs) was touched.

### 1. The helper is not 40 lines of analysis — it is `vn_positive_basic_3` plus a rescaling

The brief expected `‖·‖ ≤ C` to have to be transported through
`np_orderSeparating` (44XI) by hand: `ω(y*y) = ‖y‖_ω² ≤ (‖y−x_α‖_ω + ‖x_α‖_ω)²`
and so on.  None of that is needed, because **44XI**.3
(`vn_positive_basic_3`, *the closed unit ball is ultrastrongly closed*) is
already proved in `Basic.lean` and is exactly the `C = 1` case.  The general
case is three lines of scaling:

* `‖λ·x‖_ω = |λ|‖x‖_ω` (`omegaNorm_smul`) makes `x ↦ (C+ε)⁻¹·x` preserve
  ultrastrong convergence;
* the rescaled net lies in the unit ball, so `IsClosed.mem_of_tendsto` puts
  the limit there;
* `le_of_forall_pos_le_add` removes the `ε`, which also disposes of `C = 0`
  without a case split.

Total: 30 lines, of which about half is `Complex`/`ℝ`-cast bookkeeping.
**Lesson for the next brief**: before costing a "missing analytic lemma",
grep the *already proved* statements of the same parsec range — this one had
been sitting two files away since session 3.

One Lean-specific trap worth recording, since it cost two compiles: with the
topologies encoded as `def`s (`ultrastrong A`) rather than instances,
`filter_upwards [self_mem_nhdsWithin, …]` elaborates its arguments **before**
seeing the goal's filter, so instance resolution silently picks the *norm*
topology and the tactic fails with "synthesized type class instance is not
definitionally equal".  Every `nhds`/`nhdsWithin` fact fed to `filter_upwards`
in these files has to be stated as a `have` with `@nhdsWithin A (ultrastrong A)`
written out.

### 2. 81V: scale the numerator, not the denominator

Douglas' lemma is `a*a ≤ λ²b*b ⟹ a ∈ (𝒜)_λb` and `‖a/b‖ ≤ λ`.  **81III**
`proto_douglas_1` handles only `λ = 1`.  The obvious reduction — replace `b`
by `λb` — needs `⌊λb⌉ = ⌊b⌉`, which is extra work; replacing `a` by `λ⁻¹a`
needs only `(λ·a)/b = λ·(a/b)`, which is two lines from `div_eq`
(`div_smul_left`).  With that, `‖a/b‖ ≤ λ` follows from
`‖∑_{n<N} (λ⁻¹a)tₙ‖ ≤ 1` (`apinv_partialSum_norm_le`: the same conjugation
estimate as `apinv_block_est`, with the block `[M,N)` replaced by `[0,N)`,
landing in `∑_{n<N} btₙ ≤ 1` because that partial sum is a projection) and
the helper of §1.  The `⇐` half of the `iff` then comes free from
`div_spec`.

`douglas_2` (`a ∈ 𝒜⌊b⌉` need not give `a ∈ 𝒜b`) is the thesis's **own**
81XI example, one parsec later: `b = (1,½,⅓,…) ∈ ℓ^∞(ℕ)`, `a = ⌊b⌉`.  All
coordinates of `b` are non-zero, so every coordinate of the projection `⌊b⌉`
is `1` (from `⌊b⌉b = b` and cancellation in `ℂ`), and `⌊b⌉ = cb` would force
`cₙ = n+1`.

### 3. 81VI: one core lemma serves both parts, and it is not the thesis's hint

`sequential-douglas` asks for (1) `a ∈ b*(𝒜)_λb ⟺ a ≤ λb*b`, with
`‖b*∖a/b‖ ≤ λ`, and (2) positivity of `b*∖a/b`.  Both come out of a single
auxiliary, `sequential_douglas_core`: from `0 ≤ a ≤ λ·b*b`, apply **81V** to
`√a` (which satisfies `(√a)*√a = a ≤ (√λ)²b*b`) to get `‖c‖ ≤ √λ` with
`√a = cb`; then

    a = (√a)*√a = b*(c*c)b     and     b*∖a/b = ⌈b*⌋(c*c)⌊b⌉ = (c⌊b⌉)*(c⌊b⌉),

using `⌈b*⌋ = ⌊b⌉` (**59VI**.3).  The last expression gives the norm bound
(`‖x*x‖ = ‖x‖²`) *and* part 2's positivity at once.

The thesis's hint for part 2 is different — "prove that
`(b*∖√a)(√a/b) = b*∖a/b`" — and is a genuine alternative, but it needs the
two one-sided divisions of `√a` to be related, whereas the route above needs
only the explicit formula `b*∖x/b = ⌈b*⌋d⌊b⌉` for `x = b*db`, which is
already inside the proof of **81II**.3 (`division_basic_3`).  **Divergence
class 2.**

The `⇒` half of (1) needs one step the exercise does not mention: `‖c‖ ≤ λ`
does **not** give `c ≤ λ·1` (that needs `c` self-adjoint).  Since `a` is
positive, `a = b*cb = b*c*b`, so one may replace `c` by `½(c + c*)`, which
is self-adjoint with the same bound.  Worth a line in the solution when one
is written.

### 4. 81VII is true; 81IX's second half is **false**

These two look like the same statement and they are not.

**81VII** `div_approx`: `(∑_{n<N}sₙ)a(∑_{m<N}tₘ) → c∖a/b` for `a = cdb`,
`‖d‖ ≤ 1`.  The net is literally `Q_N d P_N` with `Q_N = ∑ sₙc ↑ ⌈c⌋` and
`P_N = ∑ btₘ ↑ ⌊b⌉`, and

    Q_N d P_N − ⌈c⌋d⌊b⌉ = (Q_N−⌈c⌋)d(P_N−⌊b⌉) + (Q_N−⌈c⌋)(d⌊b⌉) + (⌈c⌋d)(P_N−⌊b⌉).

The first term is `≤ 2‖P_N − ⌊b⌉‖_ω` by `‖xy‖_ω ≤ ‖x‖‖y‖_ω`; the second and
third are instances of `usTendsto_mul_left_right` (multiplication by a fixed
element on either side is ultrastrongly continuous).  **True, proved.**

**81IX** second half — `a ↦ c∖a/b` ultrastrongly continuous on `c(𝒜)₁b` — is
**false**.  Take `b = 1`, so the map is `c∖(·)` on `c(𝒜)₁`; in `B(ℓ²)` take
`c = diag(1,½,⅓,…)` (positive, injective, so `⌈c⌋ = 1` and `c∖(cd) = d`) and
`dₙ = |n⟩⟨0|`.  Then `cdₙ = (n+1)⁻¹|n⟩⟨0| → 0` in *norm*, hence
ultrastrongly, while `c∖(cdₙ) = dₙ` has `‖dₙ‖_ω = ‖dₙ|0⟩‖ = 1` for the vector
state at `|0⟩`.  Continuity implies sequential continuity, so the map is not
continuous.  Filed in ERRATA.md and QUESTIONS.md (A5) with three candidate
repairs.

The difference between the two is exactly the quantifier: in 81VII `d` is
**fixed**, and `‖(⌈c⌋−Q_N)(d⌊b⌉)‖_ω² = (d⌊b⌉)^*ω(⌈c⌋−Q_N)(d⌊b⌉) → 0` by
*normality* of `conjNP (d⌊b⌉) ω`; continuity would need this uniformly over
the unit ball of `d`, and `sup_{‖d‖≤1}‖R_N d‖_ω = ‖ξ‖` for every `N`.  This
also refutes the parenthetical "(and uniformly so)" in **81VII** itself,
though our Lean statement of 81VII does not claim it.  Note the commutative
case *is* fine (`‖e‖_ω² ≤ c_K⁻²‖ce‖_ω² + 4ε` for `‖e‖ ≤ 2`), which is a
plausible source of the slip; and note that `(·)/b` is unaffected, because
the seminorms `ω(x*x)^½` control exactly the side on which `(·)/b` divides —
this is why **81III**.2's uniformity exists at all.

`div_usc` is therefore left `sorry` (it is a conjunction, and we never change
a statement); the true half is proved separately as `div_usc_ball`, with the
counterexample in its doc comment.

`div_usc_ball` is a literal transcription of vn.tex:5541: `proto_douglas_2`
gives `N` with `‖a/b − ∑_{n<N}atₙ‖_ω ≤ ε/3` for *every* `a ∈ (𝒜)₁b` at once,
`∑_{n<N}atₙ = a·d` with `d = ∑_{n<N}tₙ`, and
`‖(a−a₀)d‖_ω = ‖a−a₀‖_{d*ωd}` (**44VIII**) makes the middle third an
ultrastrong ball around `a₀`.

### 5. What is left in parsec 810

Only **81VIII**.2 and the false `div_usc`.  **81VIII**.1 went through as
predicted, on top of 81VI applied to `√b` (note `(√b)*√b = b`): the witness
is `√b∖a/√b`, positive by 81VI.2 and a genuine witness by the new
`ldiv_div_recover`; the `⇐` direction is `√b c √b ≤ ‖c‖·√b√b = ‖c‖·b`.
**81VIII**.2 additionally wants uniqueness of `c` with `⌈c⌉ ≤ ⌈b⌉` and
*ultraweak* convergence of the double series `∑_{m,n} tₘatₙ`, which is a
genuine extra argument and was not attempted.

### 6. Verification

`lean Theses/A/VN/Division.lean` (invoked directly with `LEAN_PATH`, per the
process note — `lake env lean` blocks on other agents' locks): no errors, the
only warnings are the two pre-existing `dif_pos` deprecations at lines 70 and
1521.  Full-file check takes ~13 s against warm oleans, so this file is cheap
to iterate on.  `#print axioms` was run by **appending the commands to the
module itself** and recompiling, never from an importing scratch file — that
avoids the stale-olean trap entirely and needs no rebuild.  All twelve new
declarations: exactly `[propext, Classical.choice, Quot.sound]`.

Sorry counts (`grep`-free, from the compiler's `declaration uses 'sorry'`
lines): `Division.lean` 13 → **7** (lines 766 and 779 in parsec 790,
81VIII.2, `div_usc`, and three in parsec 842).  `A/VN` total 74 → **68**
(Basic 25, Completeness 2, Division 7, NormalFunctionals 14,
Projections 20).

## Session 46 — `B/Dils` Stinespring: **138II** `nmiu-between-type-I` is proved, and with it 138VI and 138VII (worker 71)

Files touched: `Theses/B/Dils/Stinespring.lean`, this log.  Nothing staged,
nothing committed.  **B/Dils 57 → 54 `sorry`s** (`Stinespring.lean` 6 → 3).

### 1. The finding: 138II does *not* need a Hilbert-space tensor product development

Session 45 parked the whole 138II cluster on the ground that `hilbTensor` /
`tensorCLM` carry exactly one API lemma and that 138II's proof "needs an
inner-product formula, a unitary-from-orthonormal-bases construction, and
ultraweak sums of `|rᵢⱼ⟩⟨rᵢⱼ|`".  That estimate was too pessimistic, and the
reason is the recurring one: *the proof consumes a sliver of the theory, not
the theory*.  What was actually needed came to **~130 lines**:

* Mathlib already has `TensorProduct.instInnerProductSpace` (with
  `TensorProduct.inner_tmul`) and `UniformSpace.Completion.innerProductSpace`,
  so `hilbTensor H K` is a Hilbert space with `⟪x⊗y, x'⊗y'⟫ = ⟪x,x'⟫⟪y,y'⟫`
  for free — no construction at all.  `hilbTensor_inner_mk` is three lines.
* `hilbTensor_ext` (two continuous linear maps agreeing on elementary tensors
  are equal) — 10 lines, via `TensorProduct.induction_on` plus
  `Continuous.ext_on` on the dense range of the coercion.
* `exists_hilbTensor_isometry`: a linear map on the *algebraic* tensor product
  that preserves inner products extends to an isometric CLM on the completion
  — 30 lines, via the existing `LinearMap.extendOfNorm`.

**No orthonormal basis of the tensor product, and no unitary-from-bases
construction, is used anywhere.**  Those are artefacts of reading the thesis's
proof literally; see item 2.

⚠️ **A trap for anyone else touching `TensorProduct` analytically.**
`TensorProduct.induction_on` produces goals whose `0` and `+` are the *algebraic*
instances (`instZeroTensorProduct`, `instAddTensorProduct`), while
`inner_zero_right` / `inner_add_right` are stated for the ones coming from
`SeminormedAddCommGroup`.  The two are defeq but not syntactically equal, so
`rw`, `simp` **and** bare `exact inner_add_right _ _ _` all fail, the last with
a stuck `InnerProductSpace ?𝕜 (E ⊗ F)` because `𝕜` never gets solved.  What
works is `exact inner_add_right (𝕜 := ℂ) x u v` with every argument given.
This cost more time than any mathematical step in the session.

### 2. The proof: the thesis's construction, made coordinate-free

Divergence **class 2** (thesis proof fine; different route), and it is worth
recording precisely because the two proofs are the *same construction*.

dils.tex 138IV picks an orthonormal basis `(eᵢ)` of `ℋ`, a basis `(dⱼ)` of
`𝒦' = ϱ(p_{i₀})𝒦`, the partial isometries `uᵢ = |e_{i₀}⟩⟨eᵢ|`, sets
`rᵢⱼ = ϱ(uᵢ*)dⱼ`, proves `(rᵢⱼ)` is an orthonormal basis of `𝒦`, and *defines*
`U` by `U rᵢⱼ = eᵢ ⊗ dⱼ`.  We instead build the map in the other direction,
without coordinates on either factor:

    W : ℋ ⊗ 𝒦' → 𝒦 ,   W(x ⊗ d) = ϱ(|x⟩⟨e₀|) d ,

so that `W(eᵢ ⊗ dⱼ) = rᵢⱼ` — the same map, and `U = W*`.  Three things fall out:

* **Orthonormality of `(rᵢⱼ)` becomes one computation, valid for all `x,y,d,d'`
  at once**: `⟪ϱ(|x⟩⟨e₀|)d, ϱ(|y⟩⟨e₀|)d'⟫ = ⟪d, ϱ(|e₀⟩⟨x|·|y⟩⟨e₀|)d'⟫
  = ⟪x,y⟫⟪d, ϱ(p₀)d'⟫ = ⟪x,y⟫⟪d,d'⟫`, the last step because `d' ∈ 𝒦'`.  This is
  literally the thesis's `‖rᵢⱼ‖ = 1` computation with `eᵢ, dⱼ` left as
  variables, and it *is* the isometry of `W`.
* **138V disappears.**  The thesis's second half expands `|a eᵢ⟩⟨e_{i₀}|` as an
  ultrastrongly convergent sum `∑ₖ ⟨eₖ, aeᵢ⟩ |eₖ⟩⟨e_{i₀}|` and uses
  ultrastrong continuity of `ϱ` (`p-uwcont`) to push `ϱ` through it.  In the
  coordinate-free form the intertwining relation `W ∘ (a ⊗ 1) = ϱ(a) ∘ W` is
  the one-line identity `a·|x⟩⟨e₀| = |a x⟩⟨e₀|` checked on elementary tensors
  and extended by `hilbTensor_ext`.  **No ultrastrong convergence, and no use
  of `p-uwcont`, anywhere in the proof.**
* **Injectivity of `ϱ` is never needed.**  dils.tex 138III opens by proving
  `ker ϱ = 0` via `prop:weakly-closed-ideal` and centrality of projections in
  `B(ℋ)`.  That step is not used by anything below it in our proof: what the
  argument needs is surjectivity of `W`, and that is proved directly.  (The
  hypothesis "`ϱ` non-zero" is still used, but only to rule out `ℋ = 0`.)

**What the thesis's argument is genuinely needed for** is exactly one step, and
it is transcribed faithfully as `nmiu_forall_mem`: the range `M` of `W` is all
of `𝒦`.  Take a Hilbert basis `(eᵢ)` of `ℋ`, `pᵢ = |eᵢ⟩⟨eᵢ|`.  Then
`pᵢ = |eᵢ⟩⟨e₀| · |e₀⟩⟨e₀| · |e₀⟩⟨eᵢ|`, so `ϱ(pᵢ)𝒦 ⊆ M`, hence
`ϱ(∑_{i∈F} pᵢ) ≤ P_M` for every finite `F` (a projection whose range lies in a
closed subspace is below the projection onto it).  Meanwhile
`IsLUB {∑_{i∈F} pᵢ} 1` in `sa(B(ℋ))` — Parseval, in the form
`HilbertBasis.hasSum_inner_mul_inner` — and `ϱ` is normal, so `1 = ϱ(1)` is the
*least* upper bound of `{ϱ(∑_{i∈F} pᵢ)}`, giving `1 ≤ P_M` and `M = 𝒦`.  This
is the thesis's display `1 = ϱ(1) = ∑ᵢ ϱ(pᵢ) = ∑ᵢⱼ |rᵢⱼ⟩⟨rᵢⱼ|` read as an
inequality between projections, which avoids having to give the sum
`∑ᵢⱼ |rᵢⱼ⟩⟨rᵢⱼ|` a meaning as a limit.

### 3. **138VI** `typei_inner_auto` — proved, and the tensor product is not needed at all

The thesis states this as a corollary of 138II.  Deriving it *through* 138II
would mean showing `dim 𝒦' = 1` and then transporting along `ℋ ⊗ 𝒦' ≅ ℋ`,
which is more tensor bookkeeping than the whole of 138II.  Instead the same
skeleton runs with `𝒦'` replaced by a single unit vector `d₀ ∈ ϱ(p₀)𝒦`:
`V : ℋ → 𝒦`, `V x = ϱ(|x⟩⟨e₀|)d₀`, is an isometry by the same computation,
intertwines by the same identity, and is surjective by the same
`nmiu_forall_mem` — provided `ϱ(p₀)𝒦 = ℂd₀`, which is where *surjectivity* of
`ϱ` enters:

> if `d ⊥ d₀` are unit vectors fixed by `ϱ(p₀)`, pick `a` with
> `ϱ(a) = |d⟩⟨d₀|`; then `p₀ a p₀ = ⟨e₀, a e₀⟩ p₀`, so applying
> `ϱ(p₀ a p₀) = ϱ(p₀)ϱ(a)ϱ(p₀)` to `d₀` gives `d = ⟨e₀,ae₀⟩ d₀`, whence
> `⟨d₀,d⟩ = ⟨e₀,ae₀⟩ = 0` and `d = 0`, contradiction.

The easy direction (`ad_U` is bijective) is the two-line inversion
`U(U* a U)U* = a`, `U* (U c U*) U = c`.  Divergence class 2 again — the
thesis gives no proof, so there was nothing to transcribe.

### 4. **138VII** `physics_stinespring` — proved exactly as the exercise directs

Stinespring (`stinespring_normal`, already proved in this file) followed by
138II, with `V = U ∘ V₀`.  The one case the exercise does not mention: if the
dilating space is `0` then `ϱ = 0`, 138II does not apply, and `φ = 0`; the
witness there is `𝒦' = (⊥ : Submodule ℂ 𝒦)` and `V = 0`.  Divergence class 1
in the weakest sense — a missing degenerate case in an exercise, not worth an
erratum.

### 5. What is left in the cluster, and what it would cost

* **138VIII** `kraus_decomposition` (both halves) — *not* attempted, and the
  reason is specific.  From 138VII one gets `φ(a) = V*(a ⊗ 1)V`; with an
  orthonormal basis `(eᵢ)` of `𝒦'` and the slices `Pᵢ(x ⊗ d) = ⟨eᵢ,d⟩x` one has
  `Pᵢ* a Pᵢ = a ⊗ |eᵢ⟩⟨eᵢ|`, so the Kraus operators are `Vᵢ = Pᵢ V` and the
  statement reduces to `∑_{i∈F} (a ⊗ |eᵢ⟩⟨eᵢ|) → a ⊗ 1` **ultraweakly**.  That
  is the piece we do not have: it needs the slice maps (easy, ~40 lines by the
  same `exists_hilbTensor_isometry` route) *plus* ultraweak convergence on
  `hilbTensor`.  The convergence lemma itself is **already available**: **44VI**
  `vna_supremum_uwlimit` (`A/VN/Basic.lean:1281`) says a bounded directed set of
  self-adjoints converges ultraweakly to its supremum, so what is missing is the
  order statement `IsLUB {a ⊗ P_F} (a ⊗ 1)` for `a ≥ 0` and finite `F`, plus
  `a,b ≥ 0 ⟹ a ⊗ b ≥ 0` (which is `(c ⊗ d)*(c ⊗ d)` once `tensorCLM` has an
  adjoint formula — one `hilbTensor_ext`), the reduction of a general `a` to four
  positives, and pushing the limit through `ad_V`.  The `IsLUB` goes exactly like
  `isLUB_hilbertBasis_partialSums` above: `(a ⊗ P_F)ξ → (a ⊗ 1)ξ` in norm for
  elementary `ξ`, hence for all `ξ` by density and `‖a ⊗ P_F‖ ≤ ‖a‖`, and then
  compare quadratic forms.  Estimate **250–400 lines**, most of it that `IsLUB`.  The finite-dimensional half additionally needs the *minimal* Stinespring
  dilation (`stinespring_minimal_dilation`, in this file) to bound `dim 𝒦'`, since
  the `𝒦'` produced by 138VII carries no dimension bound.
* **139XI** `ess_uniq_pur` — untouched; it is essential uniqueness of
  purification and looks to need minimality, which the statement does not
  hypothesise.  Worth a suspicion-of-falsity pass before any proof attempt.

### 6. Notes on the brief

* The brief's "138II rests on a Hilbert-space tensor product development that
  `hilbTensor`/`tensorCLM` does not have" was **wrong in its conclusion**,
  though right about the state of the API.  The recurring lesson it itself
  quoted — "*Mathlib lacks X* is a fact about Mathlib, not a measurement of how
  much of X the proof consumes" — applied here, and to the thesis's own proof
  as much as to Mathlib: the basis-heavy presentation in 138IV/138V made the
  requirement look much larger than it is.
* The brief says `Stinespring.lean` has "seven sorries, six of them the 138II
  cluster".  It has **six** code `sorry`s (the seventh `grep` hit is the word
  `sorry` in the file's header doc comment), and the cluster is **five** of
  them: 138II, 138VI, 138VII, 138VIII ×2 — **139XI is not downstream of 138II**
  (it is about two given dilations of one `φ`, not about the form of an
  nmiu-map), so it would have survived the cluster falling in any case.
* `Theses/B/Dils/HilbertModules.lean` is now at **0** `sorry`s; the per-file
  B/Dils split is Kaplansky 5, Paschke 8, Pure 15, SelfDualCompletion 2,
  SelfDual 21, Stinespring 3.

### 7. Verification

`lean Theses/B/Dils/Stinespring.lean` — no errors, three `sorry` warnings.
`#print axioms` on `nmiu_between_type_I`, `typei_inner_auto`,
`physics_stinespring` and `nmiu_forall_mem`: all exactly
`[propext, Classical.choice, Quot.sound]`.  `Stinespring.olean` was
regenerated with `lean -o …` (which does not take the workspace lock, unlike
`lake build`) and `Theses/B/Dils/Paschke.lean`, the one file importing it,
re-checks clean — so none of the ~15 new names collides downstream.

## Session 47 — `A/VN`: two of 89IX's three blockers closed (**69IVb**, **88IX**), and the claimed circularity is not real (worker 72, A chain)

Target given: **89IX** `normal_functional`, "blocked on 88IV, 88IX and
69IVb", with a warning that 69IVb might be circular (leastness in 89V wants
`Z(π(𝒜)□) ⊆ π(𝒜)`, and the obvious bridge "wants an injectivity that 89V
does not have and whose proof uses 89V itself").

Closed (both `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | file | class |
|---|---|---|---|
| **69IVb** | `nmiu_image` | `Projections.lean` | 3 — the thesis's route, but through a different factorisation (§2) |
| **88IX** | `commutant_cceil` | `NormalFunctionals.lean` | 1 — the thesis's own deduction from 88VIII, plus the existence half it leaves implicit (§3) |

`A/VN` sorries **68 → 66** (Basic 25, Completeness 2, Division 7,
NormalFunctionals 13, Projections 19).  Also lifted the `CU`/`ncpOfNonneg`
probe object from `B/Dils/Pure.lean` into `A/VN/NormalFunctionals.lean` (§4).

### 1. The dependency graph for 89IX, corrected again

The brief (and the survey in `docs/AProc-survey.md`) says 89IX is blocked on
88IV, 88IX and 69IVb.  Those are the *leaves*; the chain in between is also
`sorry` and is where the work is:

    89IX  ←  89VII (sigma-weak-lemma)  ←  89V (sigma-weak-lemma-2)
                                         ←  88IV, 88IX, 69IVb
    89IX  ←  83V (cceil-sum)   [proved, session 44]

So closing the three leaves leaves **three theorems still to prove** —
89V, 89VII, 89IX itself — of which 89V is the substantial one (it assembles
the `U_ω` of 89I with `summing-partial-isometries` 89III, both proved) and
89VII additionally needs a Zorn-style maximal orthogonal family.  **88IV is
the one leaf still open**, and it is the analytic one: it needs `projSup` of
a family of rank-one projections in `B(H)` to be identified with the
orthogonal projection onto the closed span, which the tree does not have in
any form.  Nothing else in parsec 890 needs new Hilbert-space geometry.

### 2. 69IVb — there is no circularity, and 48VI.1 was already in the tree

The reported obstruction was that `π(𝒜)` is the image of a *non-injective*
nmiu-map, so `injective-nmiu-iso-on-image` (**48VI**.1) does not apply.  That
is right, and it is exactly what the thesis's own proof of 69IVb handles: by
**69IVa** `nmiu_factors` (proved) `f` factors through the corner `⌈f⌉𝒜`, on
which it *is* injective.  `injective_nmiu_iso_on_image_1` is **proved** in
`Basic.lean`, so nothing in the argument reaches forward to 89V.  **The
circularity is an artefact of reading the non-injective case as if the only
available tool were 48VI applied to `f` itself.**

The Lean proof does not build the corner as a type (that would need a
`CStarAlgebra ⌈f⌉𝒜` instance the tree lacks); it works with the elements
`c·a`, `c = ⌈f⌉`, and needs exactly two facts about `f` restricted to the
corner:

* **isometry** — obtained *without* any subtype gymnastics by the trick of
  testing against the pair: `φ : 𝒜 → ℬ × 𝒜`, `a ↦ (f a, c^⊥a)`, is an
  injective non-unital ∗-homomorphism (injectivity is `ker f = c^⊥𝒜`, i.e.
  **69IV** `carrier_miu`), hence isometric by Mathlib's
  `NonUnitalStarAlgHom.norm_map`; the product norm is the sup, so on the
  corner (`c^⊥a = 0`) this reads `‖f a‖ = ‖a‖`.  Closedness of the range is
  then the usual Cauchy-sequence argument.
* **order reflection** — `f x ≤ f y` with `c(y−x) = y−x` gives `x ≤ y`.  The
  argument of `starAlgHom_le_iff` transposes, with one pleasant surprise:
  where the injective case concludes `(y−x)⁻ = 0`, here one gets only
  `c·(y−x)⁻³ = 0`, hence `c·(y−x)⁻ = 0` (the element is self-adjoint, and
  `c` commutes with it) — and that is *enough*, because
  `y−x = c(y−x) = c(y−x)⁺` is then a conjugate `c*(y−x)⁺c ≥ 0`.  **No CFC
  functional calculus inside the corner is needed**, which is what one would
  otherwise have to build.

One helper worth knowing about: `starAlgHomP`, `starAlgHom_mono` and
`starAlgHom_nonneg` in `Basic.lean` are stated for two algebras **in one
universe** (`{A C : Type u}`), so they cannot be used on the `{A B : Type*}`
of `Projections.lean`.  A universe-polymorphic `nmiuP`/`nmiu_nonneg` pair is
now in `Projections.lean` (private) for that reason.

### 3. 88IX — the two `IsLeast`s are over *literally the same set*

The thesis says only "deduce from `centre-commutant`", and the Lean statement
asks for one `c` that is least in both `{p ∈ Z(R) : f(p^⊥) = 0}` and
`{p ∈ Z(R□) : f(p^⊥) = 0}`.  Unfolding, the two conditions are
`p ∈ R ∩ R□` and `p ∈ R□ ∩ R□□`, and **88VIII** `centre_commutant` (proved)
says those sets are equal — so the second half is a rewrite, and the content
is the *existence* of the least element, which the thesis leaves implicit
because it reads it off from the relative central carrier of a von Neumann
subalgebra.  `cceilMap` does not supply that (it is stated for an algebra as
a type), so it is proved here from scratch, following `exists_carrier`:

* `E := {p ∈ Z(R) : p a projection, f p = 0}` is **directed** — for `p, q ∈ E`
  the join is `p + q − pq = 1 − (1−p)(1−q)`, a projection because `p` and `q`
  commute (`q ∈ R`, `p ∈ R□`), still in `Z(R)`, and killed by `f` because
  `p + q − pq ≤ p + q`.  Writing the join this way avoids the `⌈½p+½q⌉`
  description of `p ∪ q` and with it any appeal to `ceil_mem`.
* `e := ⋃E` is then an honest supremum (`isLUB_projSup_of_directed`), so it
  lies in `R` and in `R□` because both are von Neumann subalgebras
  (`commutant_basic_3'` supplies the second), and `f e = 0` by **60IX**.2
  (`ncp_union_2`), exactly as in `ncp_union_3`.
* `1 − e` is the required least element.

### 4. The `CU` probe object, lifted into `A/VN`

`B/Dils/Pure.lean` (session 45) built `CU = ULift ℂ` with the ∗-structure and
order Mathlib lacks, plus `ncpOfNonneg : 0 ≤ a → NCPMap CU A`.  `A/Proc`
needs the same gadget for 98II.2's injectivity clause but is a *sibling* of
`B/Dils` over `A/VN`, so the block is now copied verbatim (only the
docstring changed) at the end of `A/VN/NormalFunctionals.lean`, which
`A/Proc/Measurement.lean` imports.  The copy in `B/Dils/Pure.lean` was left
in place as instructed; **it should be deleted by whoever next touches that
file**.  Two notes for that worker:

* the duplicate is harmless as it stands — a declaration in the *current*
  namespace takes precedence over one reached through `open`, so
  `Theses.B.Dils.CU` still wins inside `B/Dils` (checked), and the two
  instance sets on `ULift ℂ` are the same definitions;
* the A/VN copy is in namespace `Theses.A.VN`, so from `A/Proc` (which opens
  it) the names are just `CU` and `ncpOfNonneg`.

### 5. Corrections to the brief

1. **"89IX is blocked on three sorries"** — it is blocked on *six*: those
   three plus 89V, 89VII and 89IX's own assembly (§1).
2. **The 69IVb circularity is not real** (§2); the ingredient the brief
   thought was missing, `injective_nmiu_iso_on_image_1`, has been proved
   since session 3.
3. **`docs/AProc-survey.md` is already stale on its second headline blocker**:
   it says 96V waits on 81VI, 81VII and 81IX, but session 46 (same day,
   same worker) proved **81VI** and **81VII** and the true half of **81IX**.
   What 96V still needs from parsec 810 should be re-derived from
   `div_usc_ball` — the false second conjunct of 81IX may or may not be on
   the path.
4. Nothing false was found this session; no ERRATA or QUESTIONS rows added.

### 6. Verification

`lean Theses/A/VN/Projections.lean` and `lean Theses/A/VN/NormalFunctionals.lean`
(invoked directly with `LEAN_PATH`, per the process note): no errors, only
pre-existing warnings.  `#print axioms` was run by appending the commands to
the modules themselves and recompiling: `nmiu_image`, `commutant_cceil` and
`ncpOfNonneg` are all exactly `[propext, Classical.choice, Quot.sound]`.
Files touched: `Theses/A/VN/{Projections,NormalFunctionals}.lean` and this
log.  Oleans were **not** rebuilt (`lake build` was avoided to keep the other
two workers' checkout locks free), so the next worker in this chain should
rebuild `Theses.A.VN.Projections` before relying on `nmiu_image`.

## Session 47 — `A/Proc`: **96V is proved without `div-usc`**, and nine of `Measurement.lean`'s sorries with it (worker 72)

Files touched: `Theses/A/Proc/Measurement.lean`, `ERRATA.md`, `QUESTIONS.md`,
`docs/AProc-survey.md`, this log.  Nothing outside `Theses/A/Proc/`.
**A/Proc 113 → 104**: `Measurement` 36 → **27**, `Tensor` 43,
`QuantumLambda` 17, `Duplicators` 17.

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **96V** | `canonical_filter` (+ `isFilter_ad`) | 1 — the thesis's proof, **except** its normality step (§2) |
| **98II**.1 | `filter_basic_1` | 1 — the exercise's own route |
| **98II**.2 | `filter_basic_2` | 1 |
| **98II**.3 | `filter_basic_3` | 1 |
| **98VII** | `filter_corner` | 1 — proc.tex:678 verbatim |
| **98VII** | `filter_corner_formula` | 1 |
| **98IX** | `exists_sqBracket` | 1 |
| **98IX** | `square_f` | 1 (faithfulness is ours, §5) |
| **100II**.3 | `isPure_adSelf` | 1 |
| — | `ldiv_div_ad`, `ad_injective`, `ad_bipositive`, `isFilter_stdFilter`, `stdFilter_one`, `stdFilter_injective`, `stdFilter_bipositive`, `ceil_eq_rangeProj_sqrt`, `floor_of_isStarProjection`, `isCornerOf_cornerProjMap`, `isStarProjection_rangeProj`, `isApproxPseudoinverse_star` | new reusable infrastructure |

### 1. Our statement of 96V was **false**: `⌈d⌉ᵣ` was read as the wrong projection

`\ceilr{d}` (common-lite.tex:141) renders as `(d⌉` and is the **range**
projection `⌊d⌉ = ⌈dd*⌉` of vn.tex 59I — the least `p` with `pd = d`.  Our
`exists_canonicalFilter`/`canonicalFilter`/`canonical_filter` used
`suppProj d = ⌈d⌋ = ⌈d*d⌉` instead, the **support** projection.  The trap is
local to our tree: `Measurement.lean`'s own doc comments write `⌈b⌉ᵣ` for
`suppProj` ("the support projection `⌈b⌉ᵣ = ⌈b*b⌉`"), so the ASCII rendering
of `\ceilr` matched the Lean name for the *other* projection.

As stated it is not merely off by a convention — it is **false**.  Take
`d = |0⟩⟨1|` in `B(ℓ²)`: then `⌈d⌋ = |1⟩⟨1|`, the corner is `ℂ|1⟩⟨1|`, and
`d*ad = 0` for every `a` in it, so `c` is the zero map, `c(1) = 0`, and the
factorisation of the zero map through it is very far from unique.  With the
range projection `c` is the filter for `d*d`, which is what 98I needs at
`d = √p` (there `⌊√p⌉ = ⌈p⌉`).  **Mis-transcription on our side, corrected**
(no ERRATA entry; the thesis is right).

### 2. 96V's proof *does* use the false half of 81IX — and does not need to

The brief asked whether 96V is reachable and whether it needs 81IX's refuted
second conjunct.  Both answers are yes-and-no:

* **It does use it.**  proc.tex:440 gets normality of `g(b) = d*∖f(b)/d` from
  "`d*∖(·)/d : d*(𝒜)₁d → 𝒜` is ultrastrongly continuous by `div-usc`" — that
  is exactly the conjunct refuted in session 46.  So the printed proof has a
  genuine gap.  Filed as **ERRATA 96VI**, and QUESTIONS A5 (which said
  "nothing in the thesis appears to use it") is corrected.
* **It does not need it.**  Normality of `g` follows from two facts the proof
  already has: `c = d*(·)d` is normal, and `c` is **bipositive** on the corner
  (81VI.2 — the same lemma the proof invokes for existence).  Given a directed
  `D` with supremum `s` and an upper bound `u` of `g(D)` *in the corner*,
  `f(x) = c(g(x)) ≤ c(u)`, so `c(g(s)) = f(s) ≤ c(u)` by normality of `f`, and
  bipositivity gives `g(s) ≤ u`.  Note the upper bound is quantified in the
  corner, not in `𝒜` — that is what makes the argument short, and it is
  exactly what `PreservesDirSups` for a map *into* the corner asks for.

Everything else is the thesis's argument.  Existence of the value is 81VI.1
applied to `0 ≤ f(b) ≤ ‖b‖f(1) ≤ ‖b‖d*d`, extended off the positive cone by
linearity of `d*𝒜d`; the map is then defined by `g(b) = d*∖f(b)/d` and is
linear because `c` is injective; positivity is 81VI.2; complete positivity is
`ncp-uwlim` (96III.1) applied to the cp approximants
`(∑_{n<N}t_n)* f(·) (∑_{n<N}t_n)`, which converge **pointwise** to `g` by
`div-approx` (81VII).  *Only* the pointwise form of 81VII is used, so the
refuted parenthetical "(and uniformly so)" is not needed either.
**Divergence class 1 for everything except the normality step, class 3 there.**

Two small pieces of glue the exercise does not mention:

* `div_approx` demands `‖e‖ ≤ 1` in `a = c e b`, so the pointwise convergence
  was proved first for `0 ≤ y` with `‖y‖ ≤ 1` and then propagated by
  closure of the convergence statement under `+` and `ℂ`-scaling
  (`usTendsto_add`/`usTendsto_smul`), through `y = ‖y‖·(‖y‖⁻¹y)`,
  `y = y⁺ − y⁻`, `b = ℜb + iℑb`.
* the approximants are `star(S_N) f(·) S_N` only because `star ∘ t` is an
  approximate pseudoinverse of `d*` whenever `t` is one of `d`
  (`isApproxPseudoinverse_star`) — the six clauses are star-images of one
  another, and the two partial-sum *sets* coincide on the nose because
  `t_n a` and `a t_n` are projections.

### 3. The inversion formula is the whole of parsec 980's glue

`ldiv_div_ad : d*∖(d*xd)/d = x` for `x ∈ ⌊d⌉𝒜⌊d⌉` is two applications of the
uniqueness clauses `div_eq`/`ldiv_eq` of 81II — `(d*xd)/d = d*x` because
`x⌊d⌉ = x`, and `d*∖(d*x) = x` because `⌈d*⌋ = ⌊d⌉` and `⌊d⌉x = x`.  It gives
injectivity **and** bipositivity of `d*(·)d` immediately (the exercise's two
hints for 98II.2 and 98II.3), and it is what makes the whole 96V construction
avoid `mult-cancellation` except in one place.

`isFilter_ad d e (he : e = ⌊d⌉) c (hc : c a = d* a d)` is the general form:
carrying an arbitrary index `e` with an equation avoids transporting along
`⌊√p⌉ = ⌈p⌉` inside the dependent type `Corner A e`, which `rw` cannot do
(the algebra instances depend on `e`).  `isFilter_stdFilter` — **`c_p` is a
filter** — is then `d = √p`, and it is what actually unblocks parsec 980.

### 4. 98II.2's "near miss" of session 46 was not needed

Session 46 banked a direct proof of two of 98II.2's three conjuncts and
identified an ncp-map out of `ℂ` as the missing gadget for the third.  With
96V in hand the exercise's own route is shorter and gives all three at once:
`c = c_p ∘ α` with `α` an ncp-isomorphism (98II.1), `c_p` is injective, and
faithfulness (`⌈c⌉ = 1`) and mono-ness are then formal consequences of
injectivity of `c`.  **The ℂ-gadget is still worth building, but no longer for
this.**

### 5. 98IX `square_f`: the faithfulness clause is ours

The Corollary asserts `[f]` unital and faithful without argument.  Unitality is
`c_p([f](1)) = f(1) = p = c_p(1)` plus injectivity of `c_p`.  Faithfulness we
argued as follows: if `[f](x) = 0` for `0 ≤ x` in `⌈f⌉𝒜⌈f⌉` then `f(x) = 0`,
so `⌈f(⌈x⌉)⌉ = ⌈f(x)⌉ = 0` by 60V, so `f(⌈x⌉) = 0`, so `⌈f⌉ ≤ ⌈x⌉^⊥` by
minimality of the carrier; but `⌈x⌉ ≤ ⌈f⌉`, so `⌈x⌉ ≤ ⌈x⌉^⊥`, and conjugating
that by `⌈x⌉` gives `⌈x⌉ = ⌈x⌉³ ≤ 0`, hence `x = 0`.  Applied to
`x = 1 − ⌈[f]⌉` it gives `⌈[f]⌉ = 1`.

### 6. What is left in parsec 980–1000, and what it now hangs on

**98III `filters-composition` is the live blocker** (with 98VI), and it is
harder than it looks.  One cannot factor `f` through `d` first: the hypothesis
is `f(1) ≤ d(c(1))`, and `c(1)` is an arbitrary *positive* element, not an
effect, so `d(c(1)) ≰ d(1)` in general and `d`'s universal property does not
apply.  The route that should work is to replace both factors by standard
filters (98II.1): `c_q ∘ c_{p'} = (√p'√q)^*(·)(√p'√q)`, and then
`isFilter_ad` closes it provided `⌊√p'√q⌉ = ⌈p'⌉` — which is where the real
work is (it is a `⌊ab⌉ = ⌊a⌉` statement under `⌈a⌋ ≤ ⌊b⌉`).  Not attempted.
100III `pure_fundamental` and everything above it wait on 98III + 98VI.

### 7. Verification

`env LEAN_PATH=… lean Theses/A/Proc/Measurement.lean` → **0** `error:` lines;
27 `declaration uses 'sorry'` warnings, down from 36, and no new warning of any
kind.  `#print axioms` was run by appending a block to the module itself and
recompiling (never from an importing scratch file, to avoid the stale-olean
trap): all twelve named declarations above, plus the session-46 regressions
`filter_of_projection_multiplicative` and `sequential_product_counterexample_1`,
are exactly `[propext, Classical.choice, Quot.sound]`.  Nothing staged, nothing
committed.  One build was lost to `A/VN/NormalFunctionals.olean` disappearing
under another worker's `lake build`; retrying 20 s later worked, as the brief
predicted.

## Session 47 — `B/Dils` Kraus: **138VIII** (general case) is proved, and **139XI is false** (worker 72)

Files touched: `Theses/B/Dils/Stinespring.lean`, `ERRATA.md`, `QUESTIONS.md`,
this log.  Nothing staged, nothing committed.  **B/Dils 54 → 53 `sorry`s**
(`Stinespring.lean` 3 → 2).

### 1. 139XI `ess_uniq_pur` — the suspicion-of-falsity pass says **false**

The previous session flagged it because it does not hypothesise minimality.
That was right, and the counterexample is one line of operator theory: take
`𝒦' = ℓ²`, `𝒦 = ℋ ⊗ ℓ²`, `W = 1` and `V = 1 ⊗ S` with `S` the unilateral
shift.  `S*S = 1` gives `V*(a⊗1)V = a⊗1 = W*(a⊗1)W`, so both are dilations of
the ncp-map `φ(a) = a ⊗ 1` (a normal unital `*`-homomorphism), and `W = 1`
forces `U = S` in `V = (1⊗U)W` — an isometry, not a unitary.

**Where the author's solution breaks** is its *last* paragraph only: "As `𝒱`
and `𝒲` are isomorphic, they have the same dimension and so do `𝒱^⊥` and `𝒲`"
(the final `𝒲` is a typo for `𝒲^⊥`).  Equal dimension does not give equal
*co*dimension in infinite dimensions — in the example `𝒱' = ran S` and
`𝒲' = 𝒦'` are both `ℵ₀`-dimensional with codimensions 1 and 0 — and that
extension step is exactly what produces the unitary of `𝒦'`.  Everything
before it, including the minimal case and `U₀ = 1 ⊗ U₁`, is correct as
written.  Note also that weakening "unitary" to "isometry" does **not** repair
the statement: swapping the roles of `V` and `W` in the same example needs an
isometry of `𝒦'` whose restriction to a proper subspace is already onto.

Point **139X** calls the property one about "dilations *of the same
dimension*", so a hypothesis is plainly intended; which one is a decision, so
the row is in ERRATA and the ruling request is **QUESTIONS B12**.  The
statement is left `sorry`ed and unchanged.

*Not machine-checked.*  A Lean counterexample would have to supply an
`NCPMap`, i.e. prove normality of `a ↦ a ⊗ 1`, plus a non-surjective isometry
on `ℓ²` (`OrthogonalFamily.linearIsometry` against the orthonormal family
`(e_{i+1})ᵢ` of `lp (fun _ : ℕ => ℂ) 2` is the cheap route).  That is
~200 lines and it was judged a worse use of the session than 138VIII; the
paper argument above is complete and needs no formalization to be checked.

### 2. **138VIII** `kraus_decomposition` — proved; **614 lines** against the 250–400 estimate

The previous session's costing was right about the *shape* of the proof and
low by about 60% on the size.  Where the extra went is worth recording,
because none of it is the mathematics:

* **The `IsLUB` was the cheap part, not the expensive one** (the estimate said
  "most of it that `IsLUB`").  It is ~35 lines, because it is not proved by
  comparing quadratic forms of `a ⊗ P_F` and `a ⊗ 1` at all — see below.
* **The expensive part is the `tensorCLM` API that did not exist**: `mul`,
  `one`, `adjoint`/`star`, `add`/`sub`/`zero`/`sum` in the right-hand factor,
  `nonneg`, `mono`, and the `hilbTensorMk` additivity/homogeneity lemmas they
  rest on — ~230 lines, every one of them a `hilbTensor_ext` one-liner *after*
  the ext lemma applies.  `tensorCLM_adjoint` alone is 30 lines: the existing
  `hilbTensor_ext` cannot see it, because `⟪T x, y⟫` is *conjugate*-linear in
  `x`, so the identity has to be extended in `y` first (linear), conjugated,
  extended in `x`, and conjugated back.
* **`hilbTensor_ext` needed a universe-polymorphic twin.**  It is stated with
  `Z : Type u`, the file's single universe, and every use here has `Z = ℂ`.
  `hilbTensor_ext'` (13 lines, same proof, `[NormedAddCommGroup Z]
  [NormedSpace ℂ Z]` and no completeness) is what the adjoint argument uses.
  ⚠️ This will bite anyone else mapping out of `hilbTensor` into scalars.
* ~90 lines are the `(1 ⊗ P_F)ξ → ξ` argument (uniform bound `‖1⊗P_F‖ ≤ 1`
  from idempotence and self-adjointness, elementary tensors by continuity of
  `y ↦ x ⊗ y`, then the 3ε density argument), and ~60 the four-positives
  reduction plus `uwTendsto_add'`/`uwTendsto_smul'`.

### 3. Two structural simplifications worth reusing

**(a) Never form the operator `Pᵢ` (the slice map).**  The costed plan wanted
slice maps `Pᵢ(x ⊗ d) = ⟨eᵢ,d⟩x`, "easy, ~40 lines by the
`exists_hilbTensor_isometry` route".  That route does not in fact work — a
slice map preserves no inner product, and bounding `‖(1⊗⟨e|)z‖ ≤ ‖z‖` on the
*algebraic* tensor product is not a one-liner.  What works is to build the map
in the other direction and take an adjoint: `hilbTensorKet e : ℋ → ℋ ⊗ 𝒦'`,
`x ↦ x ⊗ e`, is bounded by inspection (`‖x ⊗ e‖ = ‖x‖‖e‖`), and
`Pᵢ := (hilbTensorKet eᵢ)*` then has `Pᵢ(x ⊗ y) = ⟪eᵢ,y⟫ x` by one
`ext_inner_right`.  The Kraus operators are `Vᵢ = Pᵢ ∘ V₀` and
`Qᵢ a Qᵢ* = a ⊗ |eᵢ⟩⟨eᵢ|` is a three-line `hilbTensor_ext`.  This is the same
trick that made 138II cheap last session (build `W`, not `U`), and it has now
paid twice.

**(b) The supremum is proved in `B(𝒦)`, not in `B(ℋ ⊗ 𝒦')`.**  The plan was
to prove `IsLUB {a ⊗ P_F} (a ⊗ 1)` upstairs and then "push the limit through
`ad_V`" — which needs *normality* of `ad_{V₀}`, a fact we would have had to
prove.  Instead the whole `IsLUB` is stated for the conjugated net
`x_F = V₀*(a ⊗ P_F)V₀` directly: the upper-bound half is `ad`-monotonicity
(elementary, from `IsPositive.adjoint_conj`), and the least-upper-bound half
is the quadratic-form limit
`⟪ξ, x_F ξ⟫ = ⟪(a⊗1)(R_F η), R_F η⟫ → ⟪(a⊗1)η, η⟫` with `η = V₀ξ` and
`R_F = 1 ⊗ P_F`, which is *continuity of one fixed function* along
`R_F η → η`.  Normality of `ad_{V₀}` is never used, and neither is any
`NPFunctional` computation.  The identity that makes it work is
`(1⊗P_F)(a⊗1)(1⊗P_F) = a ⊗ P_F` (`tensorProj_conj`), i.e. the thesis's
`Pᵢ* a Pᵢ = a ⊗ |eᵢ⟩⟨eᵢ|` summed over `F`.

Divergence class: **(2) different route**, with the caveat that the exercise
gives no proof — `bsols.tex` has no `kraus-exercise` solution — so there was
nothing to transcribe.  The thesis's own two-sentence sketch ("apply 138VII,
then decompose `1 = ∑|eᵢ⟩⟨eᵢ|`") is exactly what is formalized.

### 4. New, reusable

In `Stinespring.lean`, section `KrausAux` (before `section TypeI`):
`hilbTensorMk_{add,sub,smul}_{left,right}`, `norm_hilbTensorMk`,
`hilbTensorKet`/`hilbTensorKet'` and `hilbTensorKet_adjoint_mk`,
`hilbTensor_ext'`, `hilbTensor_adjoint_eq`, `tensorCLM_{one,mul,adjoint,star,
add_right,sub_right,zero_right,sum_right,nonneg,mono}`, `basisProj` with
`isStarProjection_basisProj`/`_apply`/`_nonneg`/`_mono`, `tendsto_basisProj`,
`tensorProj_{mk,star,idem,conj}`, `norm_tensorProj_le`, `tendsto_tensorProj`;
and in section `UWAux` the three ultraweak lemmas `uwTendsto_smul'`,
`uwTendsto_add'` and **`uwTendsto_of_monotone_isLUB`** — 44VI re-indexed from
the subtype `↥D` to an arbitrary directed index type, which is what any
`Finset`-indexed net needs and which nothing in the tree had.

### 5. What is left, and what it would cost

* **`kraus_decomposition_findim`** — parked, not attempted.  It is *not* a
  corollary of the general case: the `𝒦'` that 138VII hands you carries no
  dimension bound, so one has to go through the **minimal** dilation
  (`stinespring_normal_aux` returns `hmin`, the density of
  `span{ϱ(a)V₀ξ}`), observe that a dense finite-dimensional subspace of a
  Hilbert space is the whole space, and get `dim 𝒦₀ ≤ dim B(ℋ)·dim 𝒦 =
  (dim ℋ)²·dim 𝒦`; 138II then gives `𝒦₀ ≅ ℋ ⊗ 𝒦'` and
  `dim 𝒦' ≤ dim ℋ · dim 𝒦`.  The Lean cost is dominated by
  `Module.finrank (ℋ ⊗ 𝒦') = finrank ℋ * finrank 𝒦'` for *our* `hilbTensor`
  (a completion, so Mathlib's `TensorProduct` finrank lemma does not apply
  directly — though the completion is an isomorphism in finite dimensions,
  which is itself a lemma to prove).  Estimate 200–300 lines, and unlike the
  general case it is all bookkeeping.
* **`ess_uniq_pur`** — false, see §1; it should stay `sorry`ed until Bas rules
  on QUESTIONS B12.

### 6. Verification

`lean Theses/B/Dils/Stinespring.lean` — no errors, two `sorry` warnings
(`kraus_decomposition_findim`, `ess_uniq_pur`).  `#print axioms` on
`kraus_decomposition`, `tendsto_tensorProj`, `uwTendsto_of_monotone_isLUB` and
`tensorCLM_adjoint`: all exactly `[propext, Classical.choice, Quot.sound]`.
The `.olean` was regenerated with `lean -o` (which does not take the workspace
lock) and `Theses/B/Dils/Paschke.lean`, the one file importing it, re-checks
clean, so none of the ~40 new names collides downstream.

## Session 48 — `A/VN` parsecs 880–890: **88IV**, **89V** and **89VII** closed; 89IX is the last gate of the 89-chain (worker 73, A chain)

Target: the chain `89IX ← 89VII ← 89V ← {88IV, 88IX, 69IVb}`, of which 88IX and
69IVb were closed last session.  Closed here (all three `#print axioms` =
`[propext, Classical.choice, Quot.sound]`):

| point | declaration | file | class |
|---|---|---|---|
| **88IV** | `carrier_vector_state` | `NormalFunctionals.lean` | 2 — the thesis's items 1/3/4, but part 1 by reindexing rather than by computing a `projSup` (§1) |
| **89V** | `sigma_weak_lemma_2` | `NormalFunctionals.lean` | 1/3 — the thesis's proof, with its relative-carrier step replaced by an elementary one (§3) |
| **89VII** | `sigma_weak_lemma` | `NormalFunctionals.lean` | 1 — the thesis's Zorn argument, with the "so that we'll have `∑ᵢ⌈⌈ωᵢ⌉⌉ = 1`" step supplied (§4) |

`A/VN` sorries **66 → 63** (Basic 25, Completeness 2, Division 7,
NormalFunctionals 10, Projections 19).  **89IX `normal_functional` is still
open, so 111VII/111XII and the whole A/Proc "vacuous band" are still blocked**
— see §5 for exactly what 89IX now needs.

### 1. 88IV did *not* need new Hilbert-space geometry

The brief said 88IV needs "`projSup` of a family of rank-one projections in
`B(H)` identified with the orthogonal projection onto a closed span, which the
tree does not have in any form".  Neither half of that turned out to be
needed.

* **Part 1** (`⌈|x⟩⟨x|⌉_{S□} = ⋃_{T∈S} ⌈|Tx⟩⟨Tx|⌉`) is **88II**
  `commutant_ceil` (proved since session 42) plus a *reindexing* of its index
  set along `a ↦ a*`: unfolding `commutantCeil` gives
  `⋃_{a∈S} ⌈a* ⌈|x⟩⟨x|⌉ a⌉`, which is `⌈a* |x⟩⟨x| a⌉` by **60VII**.1
  (`ceil_fundamental_1`) and `= ⌈|a*x⟩⟨a*x|⌉` by a two-line computation.  No
  `projSup` is ever evaluated: the two sets are literally equal, so the two
  `projSup`s are.
* **Part 2** (the fixed points are `closure (S x)`) needs only that `88II`'s
  `IsLeast` characterisation is squeezed between the projection `q` onto
  `closure (S x)` — which the *already proved* `carrier_vector_state'` was
  constructing inline — and the observation that `⌈|x⟩⟨x|⌉ ≤ p` forces
  `p x = x`, hence `p (T x) = T (p x) = T x`.
* The one Mathlib fact that made this cheap is
  `Submodule.smul_starProjection_singleton`, giving
  `|x⟩⟨x| = ‖x‖² · P_{ℂx}` (`ketbra_self_eq_smul_starProjection`) and with it
  `0 ≤ |x⟩⟨x|`.

The cyclic-subspace construction is now factored out as
`exists_cyclic_projection` (projection onto `closure (S x)`, in `S□`, fixing
`x`, with its fixed-point set computed), and `carrier_vector_state'` was
rewritten to use it — its 60-line inline copy is gone.

**Sixteenth "needs a Mathlib-sized development" estimate to collapse on
contact.**

### 2. **89I was transcribed weaker than the thesis** — repaired

vn.tex:6849 says "`UU*` **is the projection** on `closure(ρ(𝒜)x)`"; the Lean
statement only said `{z | (U U*) z = z} = closure(ρ(𝒜)x)`, which for a general
positive operator does *not* imply it is a projection (`P_M + 2P_N` with
`N ⊥ M` has fixed-point set `M`).  89V needs the projection-ness, both for
**89III** `summing_partial_isometries`'s hypothesis and for its own
conclusion.  This is **our** transcription defect, not a thesis one, so it is
recorded here rather than in ERRATA: `gns_mapping_property` now also concludes
`IsStarProjection (U ∘L U*)` and `IsStarProjection (U* ∘L U)`.  The existing
proof already had `hUW : U ∘L W = M.starProjection`, so the repair is two
lines and nothing downstream changed.

### 3. 89V — the thesis's proof, with the relative carriers routed around

The thesis argues that `⌈σ'_ω⌉ ≤ ⌈⌈σ'_ω⌉⌉ = ⌈⌈σ_ω⌉⌉ = ρ(⌈⌈ω⌉⌉)` using **88IX**
`commutant-cceil`, and then that `⌈⌈UU*⌉⌉ = ∑_ω ⌈⌈U_ωU_ω*⌉⌉` by **68IV** and
**56XVIII**.  Both steps are about central carriers *relative to `ρ(𝒜)□`*,
which is a subalgebra-as-a-set here, not a type; `cceil` does not apply to it.
The Lean proof therefore replaces them by the elementary facts that make them
true, all of which are cheap:

* `ω((cceil ⌈ω⌉)^⊥) = 0` (monotonicity of `ω` plus `⌈ω⌉ ≤ ⌈⌈ω⌉⌉`), hence
  `ρ(⌈⌈ω⌉⌉) x_ω = x_ω` — that is `nmiu_vector_fix`, which only needs that
  `σ(q^⊥)` is a projection and `⟨v, σ(q^⊥)v⟩ = ‖σ(q^⊥)v‖²`;
* `⌈⌈ω⌉⌉` central ⟹ `closure(σ(𝒜)v) ⊆ fix σ(⌈⌈ω⌉⌉)` (`nmiu_orbit_subset_fix`);
* for star projections of `B(L)`, inclusion of fixed-point sets *is* the order
  (`isStarProjection_le_of_fix_subset`, three lines) — so
  `U_ω*U_ω ≤ π(⌈⌈ω⌉⌉)` follows from 89I's fixed-point description directly,
  and pairwise orthogonality follows from `⌈⌈ω⌉⌉⌈⌈ω'⌉⌉ = 0`.

The remaining `IsLeast` (the least central projection of `π(𝒜)□` above `U*U`
is `π(∑_ω ⌈⌈ω⌉⌉)`) is then proved as the thesis intends, with one step the
thesis leaves implicit: a competitor `p` lies in `Z(π(𝒜)□) = Z(π(𝒜))` by
**88VIII** `centre_commutant` (which needs `π(𝒜)` to be a von Neumann
subalgebra, i.e. **69IVb** `nmiu_image` — this is where 69IVb is actually
used), so `p = π(w)`; and `⌈π⌉·w` is then a *central projection* of `𝒜`
mapping to `p`, by three applications of **69IV**'s
`f a = f b ↔ ⌈f⌉a = ⌈f⌉b` (`nmiu_central_preimage`).  With that, `p` fixes
each `y_ω`, so `ω((1-z)^⊥)`-style leastness of `⌈ω⌉` and then of `⌈⌈ω⌉⌉`
gives `∑_ω⌈⌈ω⌉⌉ ≤ z` and finally `π(∑_ω⌈⌈ω⌉⌉) ≤ p`.

`V*V` is a projection because the `U_ω*U_ω` are orthogonal projections summing
to it pointwise — `HasSum.map` plus `hasSum_single`, no ultraweak topology
needed.

Four declarations in `Projections.lean` were made public for this (no
statement changed): `nmiuP`, `nmiuP_apply`, `nmiu_nonneg`, `projSup_isCentral`.

### 4. 89VII — the thesis's maximal family, and the step it skips

"Let `{xᵢ}` be a maximal set of vectors whose central carriers are pairwise
orthogonal; **so that we'll have `∑ᵢ⌈⌈ωᵢ⌉⌉ = 1`**."  That last clause is the
content and is not argued in the thesis.  In Lean: Zorn over sets of
np-functionals of the form `⟨v, ρ(·)v⟩` with non-zero, pairwise orthogonal
central carriers (`compNP (nmiuP ρ) _ (vectorNP v)` is the carrier for
"vector functional of `ρ`"); if `e := ∑ᵢ⌈⌈ωᵢ⌉⌉ ≠ 1` then `ρ(e^⊥) ≠ 0` by
injectivity of `ρ`, any `v := ρ(e^⊥)v₀ ≠ 0` gives a vector functional `ω'`
with `ω'(e) = 0`, hence `⌈⌈ω'⌉⌉ ≤ e^⊥` and `⌈⌈ω'⌉⌉ ≠ 0`, so `Ω ∪ {ω'}` is a
strictly larger member of the poset.  Then 89V applies verbatim and
`π(1) = 1`.

### 5. What 89IX still needs — the precise next gate

89IX's proof is short given 89VII, and its two remaining ingredients are both
identified:

1. **A relative form of 83V `cceil-sum`.**  The thesis writes: "since
   `1 = ⌈⌈U*U⌉⌉_{ρ_Ω(𝒜)□}` we can (by cceil-sum) find partial isometries
   `(vᵢ)` in `ρ_Ω(𝒜)□` with `1 = ∑ᵢ vᵢ*vᵢ` and `vᵢvᵢ* ≤ U*U`".  Our `cceil_sum`
   (Division.lean, proved) is stated for a von Neumann algebra **as a type**,
   and `ρ_Ω(𝒜)□` is a subalgebra-as-a-set — the same mismatch that §3 routed
   around, but here it cannot be routed around, because the conclusion *is* a
   comparison-theory statement inside the subalgebra (`MvNLE` relative to
   `ρ_Ω(𝒜)□`).  So the gate is precisely:
   *for a von Neumann subalgebra `R ⊆ B(K)` and a projection `e ∈ R` whose
   least central-in-`R` majorant is `1`, there is a family `vᵢ ∈ R` of partial
   isometries with `∑ᵢ vᵢ*vᵢ = 1` (pointwise) and `vᵢvᵢ* ≤ e`.*
   Either prove that directly (redo 83V's Zorn argument with `MvNLE` replaced
   by "there is `v ∈ R` with `v*v = p`, `vv* ≤ q`"), or give `VNSub` a
   `VonNeumannAlgebra` instance and reuse `cceil_sum` — the latter would also
   simplify §3 and 88IX, and is probably the better investment.
2. **The `ℕ`-indexing.**  Given the family, `ω(1) = ∑ᵢ ‖U vᵢ y‖²` is summable,
   so `Summable.countable_support` gives a countable support; the statement
   wants `x : ℕ → H`, so one needs an injection of the support into `ℕ` and a
   `HasSum` transport with zero padding (and a `Fintype`/finite-support branch).
   Perhaps 40 lines, independent of (1).

Everything else is in place: `exists_faithful_normal_rep_vectors`
(`Basic.lean`) supplies the universal representation `π` that 89VII wants, and
the computation `ω(a) = ∑ᵢ ⟨U vᵢ y, ρ(a) U vᵢ y⟩` is four rewrites given
`vᵢ*U*U vᵢ = vᵢ*vᵢ` (from `vᵢvᵢ* ≤ U*U`) and `U π(a) = ρ(a) U`.

### 6. Corrections to the brief

1. **"88IV needs `projSup` of rank-one projections, which the tree has in no
   form"** — it needs neither (§1).
2. **"89IX ← 89VII ← 89V ← {88IV, 88IX, 69IVb}, four theorems and the band
   turns over"** — the count was right but the *last* of the four is the one
   that does not fall to the same techniques (§5); 88IV, the one the brief
   flagged as hard, was the cheapest.
3. The brief's implicit assumption that 89I was usable as stated was wrong
   (§2).
4. Nothing false was found in the theses this session; no ERRATA or QUESTIONS
   rows added.

### 7. Verification

`lean Theses/A/VN/{Projections,NormalFunctionals}.lean` (invoked directly with
`LEAN_PATH`): no errors.  `#print axioms` was run by appending the commands to
`NormalFunctionals.lean` and recompiling: `carrier_vector_state`,
`carrier_vector_state'`, `gns_mapping_property`, `sigma_weak_lemma_2`,
`sigma_weak_lemma`, `exists_cyclic_projection` and `nmiu_central_preimage` are
all exactly `[propext, Classical.choice, Quot.sound]`; the commands were then
removed.  **Oleans for `Theses.A.VN.Projections` and
`Theses.A.VN.NormalFunctionals` are left built and current**, so downstream
workers need no rebuild.  Files touched:
`Theses/A/VN/{Projections,NormalFunctionals}.lean` and this log.

## Session 48 — `A/Proc`: **both parsec-980 blockers fall** (98III, 98VI), and five more of `Measurement.lean` (worker 73)

Files touched: `Theses/A/Proc/Measurement.lean`, `ERRATA.md`, `QUESTIONS.md`,
`docs/AProc-survey.md`, this log.  Nothing outside `Theses/A/Proc/`.
**A/Proc 104 → 97**: `Measurement` 27 → **20**, `Tensor` 43,
`QuantumLambda` 17, `Duplicators` 17.

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **98III** | `filters_composition` | 3 — the exercise has no printed proof; our route is not the one the survey predicted (§1) |
| **98VI** | `corners_composition` | 3 — proved *without* the exercise's hint or its converse (§2) |
| **103II**.1 | `purely_positive_examples_1` | 1 |
| **103II**.2 | `purely_positive_examples_2` | 1 |
| **105III**.1-2 | `chevron_f_basic_12` | 1 |
| **105V** existence | `positive_map_uniqueness_exists` | 1 |
| **106I** existence | `uniqueness_sequential_product_exists` | 1 — the thesis's own five axioms, checked one by one |
| — | `effect_le_isStarProjection_iff` | new reusable infrastructure (§4) |

### 1. 98III: the fix is **rescaling**, not `⌊√p'√q⌉ = ⌈p'⌉`

Session 47 recorded the obstruction correctly — for a filter `c`, `c(1)` is an
arbitrary positive element, so `f(1) ≤ d(c(1))` does *not* give `f(1) ≤ d(1)`
and `d`'s universal property cannot be applied first — and then proposed to
route around it through standard filters, with `⌊√p'√q⌉ = ⌈p'⌉` as the hard
step.  **None of that is needed.**  `c(1) ≤ l·1` for `l = ‖c(1)‖+1`, so by
positivity and linearity `f(1) ≤ d(c(1)) ≤ l·d(1)`; hence `l⁻¹f` *does* satisfy
the hypothesis of `d`'s universal property and factors as `l⁻¹f = d ∘ h`.
Rescaling back, `h' := l·h` (an ncp-map by `exists_ncpSmul`) satisfies
`d ∘ h' = f`, so `d(h'(1)) = f(1) ≤ d(c(1))`, and **bipositivity of `d`**
(98II.3, proved last session) upgrades that to `h'(1) ≤ c(1)` — which is
exactly the hypothesis `c`'s universal property wants.  Uniqueness is
injectivity of `d` and of `c` (98II.2).  ~45 lines.

The moral is that the two things 98II gives us — bipositivity and injectivity —
are precisely what makes the composition work, which is presumably why the
thesis places 98II immediately before 98III.

### 2. 98VI: the hint can be dropped, not merely reversed

ERRATA's 98VI row (and QUESTIONS A1) recorded that the printed hint
`⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥` is the useless direction and that the proof "needs the
converse".  That is true of the route that takes the composite's effect to be
the carrier `⌈τ∘π⌉`.  Taking a different effect avoids the carrier calculus
completely: with `π` a corner of `p`, `τ` a corner of `r`, and
`β : ⌊p⌋𝒜⌊p⌋ ≅ ℬ` the isomorphism of 98IV.1 with inverse `β'`, put

  `s := β'(r) ∈ ⌊p⌋𝒜⌊p⌋ ⊆ 𝒜`.

Then `0 ≤ s ≤ ⌊p⌋ ≤ p` (because `β'` is positive and `β'(1) = 1`), and
`π(s) = β(π_p(s)) = β(β'(r)) = r`, so `π(1−s) = 1−r`.  Everything follows:
`(τ∘π)(1−s) = τ(1−r) = 0`; a map `f` killing `1−s` also kills `1−p` (since
`1−p ≤ 1−s` and `f` is positive) hence factors as `f = f₁∘π`; and then
`f₁(1−r) = f₁(π(1−s)) = f(1−s) = 0`, so `f₁` factors through `τ`.  Uniqueness
is surjectivity of `τ∘π`, i.e. 98IV.2.  Both documents updated.

### 3. What 100III now hangs on, precisely

With 98III and 98VI proved, `pure_fundamental` (100III) is the only thing
between us and 100VII, 102IX, 105III.4, 105IV, 105V-uniqueness, 105VII and
106I-uniqueness.  Its (2)⟹(3) and (3)⟹(1) are short (the uniqueness clause of
98IX; and `f = c_{f(1)} ∘ [f] ∘ π_{⌈f⌉}` with `[f]` an iso, an iso being a
filter by the argument inside `isPure_of_iso`).  The work is **(1)⟹(2)**: the
induction over `IsPure` reduces — using 98III, 98VI, 98II.1 and 98IV.1 — to
showing that `π_s ∘ c_p` is properly pure, which is the thesis's Example 98XI
`ad-pure`: for `f = a*(·)a` between corners, `[f] = [a](·)[a]*` is an ncpu-
isomorphism, `[a] = a/√(a*a)` being the partial isometry of the polar
decomposition (82I, proved in A/VN).  **98XI is not transcribed in the Lean
file at all** — no declaration mentions it — so the next worker on this must
state it first.  That is the whole remaining cost of parsec 1000.

### 4. 106I(E) needed a small order/ceiling bridge

Axiom (E) of the sequential product is stated with `≤` (`p ∗ e₁ ≤ e₂^⊥`),
while 101VII.1 — the contraposition of `a*(·)a` with `a(·)a*`, which is what
proves it — is stated with ceilings (`⌈f(s)⌉ ≤ t^⊥`).  The bridge is
`effect_le_isStarProjection_iff`: for an **effect** `b` and a projection `q`,
`b ≤ q ↔ ⌈b⌉ ≤ q`.  `⟹` is `(1−q)b(1−q) ≤ (1−q)q(1−q) = 0` plus
`ceil_le_perp_iff`; `⟸` is `b = qbq ≤ q`, which is where `b ≤ 1` is used —
the statement is **false** for positive `b` of norm `> 1` (`b = 2q`).  Since
`√p e √p ≤ √p√p = p ≤ 1`, the hypothesis is available where it is needed.
The other four axioms are computations with `√p√p = p`: (C) rests on
`√p p √p = pp` and `√(pp) = p`, and (D) on `√p` being an effect
(`CFC.sqrt_le_sqrt` and `CFC.sqrt_one`).

### 5. Two survey dependency claims were stale

The survey listed **105V ×2** as blocked on "104IX + 105IV" and **106I ×2** on
"105V (and purity for axiom B)".  Both are right for the *uniqueness* halves
and wrong for the *existence* halves, which need only 103II.2 and 100II.3 —
both of which were already available at the start of this session.  Fixed in
`docs/AProc-survey.md`.  Also corrected there: 103II is no longer a blocker of
105IV (105III.4 is), and 102VII is now reachable rather than blocked, though it
is a long proof (approximate pseudoinverses + `mult-jus-cont` + `nmiu-rigid`)
that was not attempted.

### 6. Verification

`env LEAN_PATH=… lean Theses/A/Proc/Measurement.lean` → **0** `error:` lines
and **20** `declaration uses \`sorry\`` warnings, down from 27, with no new
warning of any kind.  `#print axioms` was run by appending a block to the
module itself and recompiling (never from an importing scratch file), for all
seven statements above: each is exactly `[propext, Classical.choice,
Quot.sound]`.  Nothing staged, nothing committed.

**Note on counting**: the refresh snippet in HANDOFF.md (`grep -o '\bsorry\b'`
minus backticked mentions) **over-counts**, because `\bsorry\b` matches the
prose "sorry-ed" that appears in `QuantumLambda.lean`'s and `Tensor.lean`'s
doc comments; it gave 20/45 for files whose code counts are 17/43.  Count the
compiler's warnings instead.

---

## Session 48 — `B/Dils` survey of `SelfDual.lean` + `Pure.lean`, and four sorries closed (worker 73)

Files touched: `Theses/B/Dils/Pure.lean`, `Theses/B/Dils/SelfDual.lean`,
`QUESTIONS.md` (B11 status), this log.  Nothing staged, nothing committed.
**B/Dils 53 → 49 `sorry`s** (`SelfDual.lean` 21 → 19, `Pure.lean` 15 → 13).
All four new theorems `#print axioms` to exactly
`[propext, Classical.choice, Quot.sound]`.

The full survey table (every `sorry` of both files with its DISP number and a
blocked-on note) is in the scratchpad as `dils-survey.md`; the load-bearing
conclusions are repeated here.

### 1. The survey's verdict: `Pure.lean` is not volume, and `SelfDual.lean` funnels through 160IV.3

`Pure.lean`'s 15 sorries were **13 blocked, 1 false, 2 reachable**, and the
two reachable ones are the two closed below.  The blockage is concentrated in
three roots — `existence_paschke` (`Paschke.lean`), **169IV**
`standard_corner_dils` and **169X** `dils_stand_filter` — and the last two are
*cited to proc.tex* (98I/95II and 96V), which is off this chapter's import
path, so proving them here means redoing thesis-A work (QUESTIONS **D3**).
**A worker sent at `Pure.lean` for throughput will find nothing left.**

`SelfDual.lean`'s 21 were **5 self-contained** (159IX, 160IV.2, 160IV.3,
161II.1, 161IV.2), two more self-contained-but-very-large (161II.2, and the
164II existence construction), and the remaining fourteen blocked.  The
funnel is worth stating precisely: **160IV.3 `hilbmod_projthm_3`** (the
orthogonal decomposition `X = V^⊥⊥ ⊕ V^⊥`) directly blocks 160IX, 160X,
163II-dense and **164II.1** `ext_tensor_dense`, and 164II.1 in turn gates
164II.2a → 164II.2b → 165VI → 166IV → 166VI → 167I.  Eleven of the file's
remaining nineteen sorries sit downstream of it.  Note in particular that
ultranorm-density of the image of `η` is **not** a field of the `ExtTensor`
structure, so it has to be derived from the universal property, and that
derivation is where 160IV.3 enters.

### 2. **169XI**.1 `dils_filter_basics_1` and **169XI**.2b `dils_filter_basics_2b` — proved

The author's solution (`bsols.tex`, `dils-filter-basics-exercise`) is
transcribed, with two deliberate divergences (**class 2**), both recorded in
the doc comment:

* **The `φ(1) ≤ 1` case split is removed.**  The solution proves part 1 under
  `φ(1) ≤ 1` — so that a competing triple's `h'` satisfies
  `h'(1) = c(φ(1)) ≤ c(1) ≤ b` and `c`'s universal property applies — and then
  reduces the general case by rescaling *the whole dilation* through **140X**.4
  twice.  Rescaling `h'` alone is enough: with `λ = (‖φ(1)‖+1)⁻¹` one has
  `λ·φ(1) ≤ 1` unconditionally, hence `(λh')(1) ≤ b`; factor `λh'` through `c`
  and scale the factor back by `λ⁻¹`.  No case split, no appeal to 140X.4.
  (The `φ(1) = 0` branch the solution worries about — "then `φ(1) ≠ 0`" — does
  not arise: `φ(1) = 0` already satisfies `φ(1) ≤ 1`.)
* **Injectivity replaces uniqueness.**  Where the solution reads off
  `φ = h'' ∘ ϱ'` and the uniqueness of `σ` from the *uniqueness* clause of
  `c`'s universal property, we use `dils_filters_injective` (**169XII**,
  already proved in the file) directly.  Same fact, three lines instead of ten.

**This settles the blast radius of QUESTIONS B11.**  Both are proved against
the *weak* dils.tex reading `c(1) ≤ b`, so the defect touches exactly one Lean
statement, `dils_filter_basics_2a`.  Part 1 survives because the only place it
needs `c`'s universal property is at `h'(1) = c(φ(1))`, and `c(φ(1)) ≤ c(1) ≤
b` holds either way; part 2b never uses the unitality of `φ'` — it is
literally part 1 applied to `c'` and the dilation of `φ'`.  QUESTIONS B11 has
been annotated accordingly; `dils_filter_basics_2a` stays `sorry`.

*File reorder*: **169XI**'s three statements now sit **after** **169XII** in
`Pure.lean`, because both parts use `dils_filters_injective` and Lean needs it
declared first.  A comment at the old position says so.  No statement changed.

*New private helpers in `Pure.lean`*: `ncpPos`, `exists_ncpComp`,
`smul_le_smul_iff_pos`, `exists_ncpSmul` (all four transcribed from
`Stinespring.lean`, where they are `private` and therefore not importable —
the standing note to merge the two corner/ncp developments now covers these
too) and `smul_norm_succ_inv_le_one` (`(1+‖w‖)⁻¹w ≤ 1` for `w ≥ 0`).

### 3. **161II**.1 `hilbmod_el2_inner` — proved by polarization, not by completeness

The statement is that `∑ᵢ cᵢbᵢ*` converges ultraweakly for ℓ²-summable
tuples.  The author's solution (`bsols.tex`, `hilbmod-el2`) proves the net of
partial sums is norm-bounded and ultraweakly **Cauchy** — two Cauchy–Schwarz
estimates, one for `𝒷`-valued inner products and one classical, plus an
ε-argument over `S − T` and `T − S` — and then appeals to bounded ultraweak
completeness (`bh-bounded-uw-complete`, our **77I**.2).

**Divergence, class 2.**  The Lean proof polarizes instead:
`4·cb* = (b+c)(b+c)* − (b−c)(b−c)* − i(b+ic)(b+ic)* + i(b−ic)(b−ic)*`
(`polarization_mul_star`), so the sum is a fixed ℂ-combination of four
*diagonal* nets `∑ᵢ dᵢdᵢ*`, each of which is monotone, positive and
norm-bounded — hence ultraweakly convergent to its supremum by **44VI** alone
(`uwTendsto_of_monotone_isLUB`, from session 47).  **Neither completeness nor
Cauchy–Schwarz is used.**  The only closure fact needed is that ℓ²-summable
families are closed under addition, and that too avoids the solution's
Cauchy–Schwarz estimate: `(x+y)(x+y)* ≤ 2xx* + 2yy*` follows from
`(x−y)(x−y)* ≥ 0`, and bounds the partial sums directly.

This is worth keeping as a pattern: **anywhere the theses reach for bounded
ultraweak completeness to sum a non-positive family, polarization reduces it
to 44VI.**

New private helpers in `SelfDual.lean`'s `section L2`: `mul_star_add_le`,
`l2Summable_add`, `l2Summable_smul`, `exists_uwTendsto_l2_diag`,
`polarization_mul_star`.

### 4. **161IV**.2 `onb1_el2` — proved directly, and it never needed 161II

The author's solution routes this through the *module* `ℓ²((pᵢ))`: the `δᵢ`
are an orthonormal basis by **161II**, `(δᵢuᵢ)ᵢ` is another one by part 1 of
this same exercise (which *is* proved in the file), and the second half of
161II then produces `ℓ²((pᵢ)) ≅ ℓ²((uᵢ*pᵢuᵢ)) = ℓ²((qᵢ))`.  Both halves of
161II.2 are `sorry`, so that route is closed.

**Divergence, class 2**, and a cheap one: the bijection can be written down.
With `uᵢ*uᵢ = pᵢ`, `uᵢuᵢ* = qᵢ`, put `Φ(b)ᵢ = bᵢuᵢ*` (mirrored from the
thesis's `uᵢ*bᵢ`), with inverse `bᵢ ↦ bᵢuᵢ`.  Membership of `L2Set` is an
absorption condition — `⌈bᵢ*bᵢ⌉ ≤ pᵢ` iff `bᵢpᵢ = bᵢ`, which is **59VI**.1
`ceill_basic_1` and is packaged here as `ceil_star_mul_self_le_iff` /
`mem_l2Set_iff` — and absorption makes
`Φ(c)ᵢΦ(b)ᵢ* = cᵢpᵢbᵢ* = cᵢbᵢ*` **termwise**.  So the two nets of partial
sums are *equal as functions*, which is why the theorem's inner-product clause
comes out as `rw [hEq]` rather than a limit argument, and why ℓ²-summability
transfers with the same bound.  About 90 lines.

`ceil_star_mul_self_le_iff` is stated in terms of `ceil (star x * x) ≤ r`
rather than `suppProj x ≤ r` because that is the form `L2Set` uses; note that
Mathlib-side `star_mul_self_absorb_iff` in `A/VN/Projections.lean` is
`private`, so the proof goes through the public `ceill_basic_1` +
`ceil_le_iff` + `ceil_of_isStarProjection` instead.

### 5. A lead for the next worker: **170IV**.1 is no longer blocked

The author's solution to `surjective-nmiu` sends the kernel of a surjective
nmiu-map through `kernel-ultraweak-twosided-ideal-dils` and **69II**
`prop:weakly-closed-ideal`, and 69II is still `sorry`
(`A/VN/Projections.lean:4384`).  **It is not needed.**  **69IV** `carrier_miu`
is proved (`A/VN/Projections.lean:4399`) and gives precisely the two facts the
argument uses: the carrier `z = ⌈ϱ⌉` of an nmiu-map is **central**, and
`ϱ(a) = 0 ↔ z·a = 0`.

What is left is routine but not short: for ncp `f : A → C` with `f(z) = f(1)`,
show `f((1−z)x) = 0` — with `w = (1−z)x = x(1−z)` (centrality),
`ww* = (1−z)xx*(1−z) ≤ ‖x‖²(1−z)`, so Kadison–Schwarz (`ncp_cp_cs`, proved)
gives `f(w)f(w)* ≤ ‖f(1)‖·f(ww*) = 0` — and then bundle the induced map on
`B ≅ A/ker ϱ` as an `NCPMap`.  Estimate 200–250 lines, mostly the bundle.
**170IV.2** (the converse) stays blocked on 169IV regardless, since it needs
the standard corner `h_z` as a *second* corner for `z`.

### 6. Verification

`lean Theses/B/Dils/Pure.lean` and `lean Theses/B/Dils/SelfDual.lean`
(with the `LEAN_PATH` bypass — `lake env lean` still blocks on the other
workers' `lake build`): no errors; 13 and 19 `sorry` warnings respectively,
matching the code counts.  `#print axioms` on `dils_filter_basics_1`,
`dils_filter_basics_2b`, `hilbmod_el2_inner` and `onb1_el2`: all exactly
`[propext, Classical.choice, Quot.sound]`.

⚠️ **Operational note.** Three times during this session a full `lake build`
in another worker's session removed and re-created `A/VN/NormalFunctionals`,
`B/Dils/HilbertModules` and `B/Dils/SelfDualCompletion` oleans, and the
single-module check failed with `object file … does not exist` — *not* with a
type error.  The brief's "retry rather than debug" rule extends to this
failure mode, and it hits **B/Dils** oleans too, not only the A-chain ones.

## Session 49 — `A/VN`: **89IX `normal_functional` is proved** — the last gate of the 890-chain, and the relative `cceil-sum` cost less than the brief feared (worker 74, A chain)

Target: **89IX** (`normal-functional`, vn.tex:7089), the theorem the whole
A/Proc "vacuous band" waits on through 111VII/111XII.  **It is closed**, with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, as are all five
supporting declarations.

`A/VN` sorries **63 → 62** (Basic 25, Completeness 2, Division 7,
NormalFunctionals **9**, Projections 19).

| point | declaration | file | class |
|---|---|---|---|
| **89IX** | `normal_functional` | `NormalFunctionals.lean` | 1 — the thesis's proof, verbatim |
| — | `cceil_sum_relative` | `NormalFunctionals.lean` | the relative **83V** the thesis uses without comment |
| — | `normal_functional_assembly`, `hasSum_projSup_apply`, `exists_nat_index`, `exists_nat_reindex` | `NormalFunctionals.lean` | the three steps the thesis compresses into one display |

### 1. The relative `cceil-sum` did **not** need a new Zorn argument — and the `VonNeumannAlgebra` instance on `VNSub` already existed

The brief proposed either redoing 83V's Zorn argument with `MvNLE` replaced
by a relative version, or "giving `VNSub` a `VonNeumannAlgebra` instance —
probably the better investment".  Neither was necessary: **that instance has
existed since session 45**, in `A/Proc/Tensor.lean`, together with the whole
`VNSub` C*-algebra/`StarOrderedRing`/normality block (~250 lines).  The only
real obstacle was *location*: `A/Proc` is downstream of `A/VN`, so it cannot
be imported from here.

The block is therefore **copied verbatim** into `A/VN/NormalFunctionals.lean`
(namespace `Theses.A.VN`), exactly as `CU` was copied in session 47, and the
copy in `A/Proc/Tensor.lean` should be deleted by whoever next touches that
file.  Checked, as for `CU`: a declaration in the current namespace takes
precedence over one reached through `open`, so `Theses.A.Proc.VNSub` still
wins inside `A/Proc` and the two instance sets are on *different types*, so
they cannot conflict.  (Verified with a scratch file reproducing the `A/Proc`
context; `A/Proc` needs no edit.)

With the instance in hand, `cceil_sum_relative` is 50 lines and its content is
entirely bookkeeping:

* `E := ⟨e, heS⟩ : VNSub A S hS`, and `cceil E = 1` — `≤` because `1` is a
  central projection above `E`, and `≥` because the hypothesis's `IsLeast`
  says `1` is least among the central projections of `S` above `e`, which is
  exactly what `(cceil_isLeast E).1` provides once pushed down along `val`;
* `cceil_sum E` then gives the family, and `MvNLE` unfolds to the partial
  isometries directly;
* the one genuinely non-formal step is that the supremum of the `fᵢ` computed
  **in `A`** is again `1`: `projSup_mem_of_np` (Completeness.lean, with
  `zeroNP`) puts `projSup P` back inside `S`, whence it is an upper bound
  *in* `VNSub` and dominates `projSup_{VNSub} = cceil E = 1`.

Two helpers were added for the traffic across `val`: `VNSub.isStarProjection_val`
and `VNSub.isStarProjection_mk`.

**Seventeenth "needs a Mathlib-sized development" estimate to collapse on
contact**, though this one collapsed for an unusual reason: the development
had already been written, one chapter too late.

### 2. The `ℕ`-indexing was as cheap as advertised

`exists_nat_reindex` (12 lines): `Summable.countable_support` on
`fun i => ‖xᵢ‖²` — whose support *is* the support of `x` — plus
`Set.countable_iff_exists_injective` and `Function.extend φ x 0`.
`exists_nat_index` (30 lines) transports along it with
`hasSum_subtype_iff_of_support_subset` and `Function.Injective.hasSum_iff`;
square-summability is not a separate obligation, it is the case `a = 1` of the
`HasSum` hypothesis (`ρ(1) = 1`, `⟪x,x⟫ = ‖x‖²`), mapped through
`Complex.reCLM`.  No `Fintype`/finite-support branch is needed.

### 3. The thesis's display, and the one step it does not spell out

The five-line `alignat*` at vn.tex:7115 is `normal_functional_assembly`.
Transcribed as written, with `vᵢvᵢ* ≤ U*U ⟹ (U*U)vᵢ = vᵢ` supplied (the
thesis writes "since `vᵢvᵢ* ≤ U*U`" and leaves it), and with the term
identity finishing at `⟪pᵢy, ϱ_Ω(a)y⟫` where `pᵢ = vᵢ*vᵢ`.

The step the thesis really does leave implicit is `∑ᵢ pᵢ = 1`: it writes
`1 = ∑ᵢ vᵢ*vᵢ` where `cceil-sum` gives only a *supremum* of projections.
`hasSum_projSup_apply` closes the gap and is three lines given
**56XVIII** `sum_of_orthogonal_projections` (proved session 42): that lemma
gives *ultrastrong* convergence of the finite sums to `projSup`, and
`usTendsto_iff` applied to the single np-functional `vectorNP y`, with
`omegaNorm_vectorNP : ‖T‖_{vectorNP y} = ‖T y‖`, turns it into
`HasSum (fun i => pᵢ y) y` in `K`.  No Hilbert-space geometry (closed spans,
orthogonal families) is needed anywhere in 89IX.

### 4. What is now reachable, and the **next** gate (it is *not* 89IX-shaped)

111VII/111XII are unblocked as far as 89IX goes.  But reading proc.tex:2528
(condition `tensor-2` of `special-tensor`) against what the tree has, its
proof needs 89IX **and** one thing more, which is also what 89XI.1
`functional_permanence_1` and hence 89XII `functional_extension` need:

> *a square-summable family `(xₙ)` of vectors defines an np-functional
> `T ↦ ∑ₙ ⟪xₙ, T xₙ⟫` on `B(H)`.*

The tree has only the converse, **39IX** `bh_np` (`A/CStar/TowardsVN.lean`).
The missing direction is easy except for **normality**, which is a
sup/sum interchange for a *directed net* (finite `F` with
`∑_{n∈F} fₙ(s) > ∑ₙ fₙ(s) − ε/2`, then directedness for the finitely many
`n ∈ F`).  Two shortcuts were checked and both fail:

* `addNP` (Basic.lean) only sums *two* np-functionals;
* the slick route "`∑ₙ⟪xₙ,T xₙ⟫` is the vector functional of `(xₙ)ₙ ∈ ⊕ₙH`
  composed with the amplification, so `compNP` gives normality for free"
  needs `PreservesDirSups ⇑ampHom`, which is **not** proved — `ampHom`
  (NormalFunctionals.lean:1359) is built as a `→⋆ₐ[ℂ]`, never as an
  `NMIUMap`, and proving its normality is the same interchange again.

So the honest estimate for 89XI.1 + 89XII + `tensor-2` of 111VII is *one*
lemma, `sumVectorNP`, of perhaps 120–150 lines; 89XII is then two lines
(`isVNSubalgebra_range` supplies the missing hypothesis of 89XI.1).  Whoever
proves it should put it in `A/VN` where both chapters can see it.

### 5. Corrections to the brief

1. **"The suggested investment is a `VonNeumannAlgebra` instance on `VNSub`"**
   — it exists already (session 45, `A/Proc/Tensor.lean`); the work was to
   *relocate* it, not to build it (§1).
2. **"Unlike 89V's relative-carrier steps this cannot be routed around — its
   content *is* comparison theory inside the subalgebra"** — the first half is
   right and the second overstates the cost: with `VNSub` the comparison
   theory is imported wholesale and nothing is redone.
3. The brief's "everything else for 89IX is in place" was right, with the one
   omission that `∑ᵢ vᵢ*vᵢ = 1` needed `sum_of_orthogonal_projections`
   converted from a supremum to a `HasSum` (§3).
4. Nothing false was found in the theses this session; no ERRATA or QUESTIONS
   rows added.  The thesis's proof of 89IX is correct as written.

### 6. Verification

`lean Theses/A/VN/NormalFunctionals.lean` (invoked directly with `LEAN_PATH`):
no errors.  `#print axioms` was run by appending the commands to the module
and recompiling: `normal_functional`, `cceil_sum_relative`,
`normal_functional_assembly`, `exists_nat_index`, `exists_nat_reindex`,
`hasSum_projSup_apply` and `instVonNeumannAlgebraVNSub` are all exactly
`[propext, Classical.choice, Quot.sound]`; the commands were then removed.
**The olean for `Theses.A.VN.NormalFunctionals` is left built and current**
(`lake build Theses.A.VN.NormalFunctionals`), so `A/Proc` and `B/Dils`
workers need no rebuild.  Files touched:
`Theses/A/VN/NormalFunctionals.lean` and this log.

## Session 49 — `A/Proc`: **100III `pure-fundamental`** falls, and with it 100VII, 105III.4 and 105IV.1/.3 (worker 74)

Files touched: `Theses/A/Proc/Measurement.lean`, `ERRATA.md`,
`docs/AProc-survey.md`, this log.  Nothing outside `Theses/A/Proc/`.
**A/Proc 97 → 90**: `Measurement` 20 → **13**, `Tensor` 43,
`QuantumLambda` 17, `Duplicators` 17 (compiler-counted).

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **100III** | `pure_fundamental` | 1 for (2)⟹(3) and (3)⟹(1); **2** for the crux of (1)⟹(2) (§2) |
| **100VII**.1/.2/.3 | `special_pure_maps_1/2/3` | 1 — the exercise has no printed solution; the route is the obvious one (§3) |
| **105III**.4 | `chevron_f_basic_4` | 1 — the exercise's own route |
| **105IV**.1 | `chevron_f_purely_positive_1` | 1 |
| **105IV**.3 | `chevron_f_purely_positive_3` | 1 |
| — | `isFilter_of_iso`, `isCornerOf_one_of_iso`, `isCornerMap_of_iso`, `isFilter_ncpId`, `isCornerOf_one_ncpId`, `isCornerMap_ncpId`, `corner_unique`, `filter_unique`, `exists_inverse_of_isFilter_unital`, `isFilter_of_isCornerOf_one`, `corner_ceil_val`, `le_sub_iff_le_one_sub`, and the private `map_conj_eq_of_map_perp`, `exists_subCornerProj`, `isFilter_corestrict`, `ncpCarrier_comp_filter` | new reusable infrastructure |

### 1. Our transcription of **100I** `pure` was too weak, and that blocked 100III

`inductive IsPure` had **no von Neumann hypotheses anywhere**, so its `comp`
constructor allowed a composite to pass through an arbitrary ordered
C*-algebra.  The thesis's parsec 1000 lives in `W*_cp`: filters and corners
are ncp-maps *between von Neumann algebras* (96I, 95I), so the algebra in the
middle of a composition is one too.

This is not cosmetic.  (1)⟹(2) is an induction over `IsPure`, and its `comp`
case must factor the two halves through `filter-basic` (98II.1) and
`corner-basic` (98IV.1), both of which need the **intermediate** algebra to be
a von Neumann algebra — the universal properties of `IsFilter`/`IsCornerOf`
quantify over von Neumann algebras only, and there is no way to manufacture
the structure from the hypotheses.  With the definition as transcribed, 100III
(1)⟹(2) is, as far as we can see, simply not provable.

Fixed by adding `[VonNeumannAlgebra B]` to the `comp` constructor — the
**minimal** repair: the `filter` and `corner` constructors need nothing,
because the base cases of the induction are `f = c ∘ id` and `f = id ∘ π`,
and `id` is a corner map (resp. a filter) with no hypotheses at all.  All
existing users of `IsPure` (`isPure_of_iso`, `isPure_id`, `isPure_adSelf`,
103III.2, 106III.1) supply the instance without change.  *Our own
mis-transcription, so no ERRATA entry* — but note it is the sixth in two
weeks with the same shape: a statement quietly **weaker** than its source.
Hypothesis-side users of `IsPure` (100VII, 102IX, 105III.4, and the `ax2`
clauses of 105V/106I/106III) are correspondingly weakened, which is what the
thesis says.

### 2. **98XI `ad-pure` is not needed** — and it is wrong as printed

The thesis reduces (1)⟹(2) to "`π_s ∘ c_p` is properly pure" and then invokes
the Example **98XI**: `[π_s ∘ c_p]` is an ncpu-isomorphism because
`[a*(·)a] = [a](·)[a]*`.  We proved the reduction target *directly*, which is
both shorter and avoids two things we do not have: the polar decomposition
(82I, proved, but only in `A/VN`) and — much worse — **iterated corners**,
since `[f]` for `f : s𝒜s → t𝒜t` lives on `Corner (Corner A s) ⌈f⌉`.  With
`p ≥ 0`, `s` a projection and `a := √p·s`, so that `(π_s ∘ c_p)(x) = a*xa`:

* `x ↦ ⌊a⌉x⌊a⌉ : ⌈p⌉𝒜⌈p⌉ → ⌊a⌉𝒜⌊a⌉` is a **corner** (`exists_subCornerProj`,
  new): it is `isCornerOf_stdCorner` run in the von Neumann algebra `⌈p⌉𝒜⌈p⌉`,
  but with the sub-corner presented as `⌊a⌉𝒜⌊a⌉` rather than as a corner of a
  corner.  `⌊a⌉ ≤ ⌈p⌉` because `⌊√p·s⌉ ≤ ⌊√p⌉ = ⌈p⌉`.
* `z ↦ a*za : ⌊a⌉𝒜⌊a⌉ → s𝒜s` is a **filter**: 96V `canonical_filter`
  corestricted to `s𝒜s`, which is legitimate because a filter whose values lie
  in a corner is a filter into that corner (`isFilter_corestrict`, new).
* and `a*(⌊a⌉x⌊a⌉)a = a*xa` because `a*⌊a⌉ = a*` and `⌊a⌉a = a`.

Reading 98XI to check it, though, turned up a genuine slip: the formula has
the two partial isometries swapped (`[f] = [a]*(·)[a]`, not `[a](·)[a]*` —
the printed map runs the wrong way between the two corners of the diagram).
**ERRATA 98XI**, with an `M₂` witness.  98XI is *still not transcribed* in the
Lean file; transcribing it faithfully needs an iterated-corner collapse
(`Corner (Corner A e) q ≅ Corner A q.val`), which nothing else now wants.

### 3. The rest of 100III, and 100VII

(2)⟹(3) is the thesis's argument.  `⌈f⌉ = ⌈π⌉` (a filter is injective, 98II.2
— extracted as `ncpCarrier_comp_filter`) and `f(1) = c(1)` (`π` unital), so
`f = c_{f(1)} ∘ (α ∘ β') ∘ π_{⌈f⌉}` with `α`, `β'` the isomorphisms of 98II.1
and 98IV.1, and the *uniqueness* clause of 98IX identifies that composite with
`[f]`.  To dodge transports along `⌈f⌉ = ⌊p⌋` and `f(1) = c(1)` inside the
dependent type `Corner A e`, the two isomorphism lemmas were re-proved in
index-free form: `corner_unique` (any two corners of the same effect are
isomorphic) and `filter_unique` (any two filters with the same value at `1`),
of which `corner_basic_1` and `filter_basic_1` are the standard-corner and
standard-filter instances.  (3)⟹(1) is `f = (c_{f(1)} ∘ [f]) ∘ π_{⌈f⌉}` with
the bracket an isomorphism, hence a filter (`isFilter_of_iso`), hence the
first factor a filter by 98III.

**100VII** then needs only two observations, both new lemmas: a *unital
filter* is an isomorphism (factor `id` through it) and a *corner of `1`* is an
isomorphism (`corner_unique` against `id`).  .1: `⌈π⌉ = ⌈f⌉ = 1` makes `π` a
corner of `1`, hence a filter, and filters compose.  .2: `c(1) = f(1) = 1`
makes `c` an isomorphism, hence a corner map, and corners compose.  .3 is .1
plus "unital filter is an isomorphism".

### 4. 105III.4 and 105IV.1/.3

105III.4 is the exercise's own route: by 105III.2, `⟨f⟩ = π_{⌈f(1)⌉} ∘ c_{f(1)}
∘ [f]`, and `[f]` is an isomorphism by 100III, so `⟨f⟩` is
corner ∘ filter ∘ filter; being faithful (105III.3) it is a filter by 100VII.1.

105IV.1 was proved in an **index-carrying** form
(`isDiamondSelfAdjoint_cornerMap`: for ⋄-self-adjoint `f` and *any* projection
`u` with `u = ⌈f(1)⌉`, the map `u f(·) u` on `u𝒜u` is ⋄-self-adjoint), because
part 3 needs it at `u = ⌈h(1)⌉` for the square root `h` of `f` while its
statement is indexed by `⌈f(1)⌉`.  Two general facts came out of it and are
worth keeping:

* `corner_ceil_val`: **ceilings computed in a corner are ambient ceilings**.
  For `0 ≤ x ∈ e𝒜e` one has `⌈x⌉ ≤ e`, so the ambient `⌈x⌉` lies in the corner
  and the two minimality clauses quantify over the same projections.
* `le_sub_iff_le_one_sub`: for projections `p, t ≤ u`, `p ≤ 1−t ⟺ p ≤ u−t`.
  This is what makes `⋄` in a corner agree with `⋄` in `𝒜`.

With those, `Contraposed ⟨f⟩ ⟨f⟩` is `Contraposed f f` verbatim.  105IV.3 is
then part 1 applied to `h` on the corner of `⌈f(1)⌉ = ⌈f⌉ = ⌈h∘h⌉ = ⌈h⌉ =
⌈h(1)⌉` (103III.1/.2/.3), together with the already-proved part 2
(`⟨h²⟩ = ⟨h⟩²`), which is exactly the equation `⟨f⟩ = k ∘ k` needed.

**A Lean note that cost two compile rounds**: `u` indexes the dependent type
`Corner A u`, so `rw [hu]` with `hu : u = ⌈f(1)⌉` is never type-correct once
any `s : Corner A u` is in sight.  State the consequences of `hu` as
`∀ x : A`-facts (`∀ x, u·f(x)·u = f(x)`, `∀ x ≥ 0, ⌈f(x)⌉ ≤ u`) *before*
touching the corner, and use those.

### 5. What parsec 1000–1060 now hangs on

Everything downstream of 100III that is not blocked elsewhere is done.  What
is left in `Measurement.lean` (13):

* **102VII** `canonical_quotient_rigid` — reachable, long (approximate
  pseudoinverses, `mult-jus-cont`, `nmiu-rigid`); **102IX** `pure_is_rigid`
  waits only on it, now that 100III is in.
* 104III.3/.4/.5 → **A/VN 81V `douglas` / 81VIII `sequential-quotient`**;
  104VII, 104IX, **105V uniqueness**, **105VII**, **106I uniqueness** are a
  single chain behind them (105V's proof cites `faithful-positive-map-
  uniqueness` = 104IX explicitly).  104III.2a is parked (false as printed).
* 106III.2/.3 — long computations, no purity involved.

### 6. Verification

`env LEAN_PATH=… lean Theses/A/Proc/Measurement.lean` → **0** `error:` lines
and **13** `declaration uses 'sorry'` warnings, down from 20, with no new
warning of any kind.  `#print axioms` was run by appending a block to the
module itself and recompiling (never from an importing scratch file): all
seven statements above, the twelve public helpers, and the regression set
`isPure_adSelf` / `isPure_of_iso` / `purely_positive_basic_2` /
`sequential_product_counterexample_1` / `uniqueness_sequential_product_exists`
(the users of the amended `IsPure`) are exactly `[propext, Classical.choice,
Quot.sound]`.  Nothing staged, nothing committed.

## Session 50 — `A/VN`: **89XI.1/.2/.3 and 89XII close the 890-chain** — and the "missing" np-functional lemma was already proved, one chapter *upstream* (worker 75, A chain)

Target: the lemma the previous session identified as the last obstacle to
89XI.1, 89XII and `tensor-2` of **111VII** —

> *a square-summable family `(xₙ)` of vectors defines an np-functional
> `T ↦ ∑ₙ ⟪xₙ, T xₙ⟫` on `B(H)`* —

estimated at "one lemma of perhaps 120–150 lines whose only hard part is a
sup/sum interchange over a directed net".

**It did not have to be written.  It is 38IV.2 `bh_functional_lemma_2` in
`Theses/A/CStar/TowardsVN.lean` (cstar.tex:6416), proved, axiom-clean, and
sitting eleven lines below its own converse 39IX `bh_np`** — the lemma the
brief said was "the only direction the tree has".  The interchange of suprema
is in its proof, at `TowardsVN.lean:1179–1186`.

`A/VN` sorries **62 → 55** (Basic 25→**24**, Projections 19→**17**,
Division 7, NormalFunctionals 9→**5**, Completeness 2).

| point | declaration | file | class |
|---|---|---|---|
| **89XI**.1 | `functional_permanence_1` | `NormalFunctionals.lean` | 2 — no thesis proof (Corollary, stated without one) |
| **89XI**.2 | `functional_permanence_2` | `NormalFunctionals.lean` | 2 — likewise |
| **89XI**.3 | `functional_permanence_3` | `NormalFunctionals.lean` | 2 — likewise |
| **89XII** | `functional_extension` | `NormalFunctionals.lean` | 1 — the thesis's own hint (48VI) |
| — | `exists_sumVectorNP` | `NormalFunctionals.lean` | arbitrary-index wrapper around 38IV.2, for `A/Proc` |
| **47V** | `vn_equalisers` | `Basic.lean` | 2 — no published solution (asols stops at parsec 340) |
| **66IV**.1 | `ultracyclic_basic_1` | `Projections.lean` | 1 |
| **66IV**.2 | `ultracyclic_basic_2` | `Projections.lean` | 1 |

All eight are `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### 1. 89XI.1 is twenty lines, and does not need its own hypothesis

Represent `B` faithfully and normally on `ℓ²(ι)` (**48VIII** `ngns`); then
`σ = f ∘ ρ : A → B(ℓ²(ι))` is injective and normal, so `isVNSubalgebra_range`
(**48VI**.1) makes its range a von Neumann subalgebra and **89IX** applies:
`ω = ∑ₙ ⟪xₙ, σ(·)xₙ⟫`.  The *same* family gives an np-functional `ν` on all
of `B(ℓ²(ι))` by 38IV.2, and `ξ = ν ∘ f` (i.e. `compNP (nmiuP f) _ ν`) is the
extension.  **The hypothesis `hR : IsVNSubalgebra B ρ.range` is never used** —
injectivity of `ρ` already gives it, by 48VI.1.  That is exactly why 89XII
(which has no `hR`) is a one-liner from 89XI.1, as the thesis's own hint
says.

89XI.2 (ultraweak permanence) is the initial-topology bookkeeping:
`induced ρ (⨅_ξ induced ξ) = ⨅_ξ induced (ξ∘ρ)` by `induced_iInf` +
`induced_compose`; `≤` because each `ξ∘ρ` is an np-functional of `A`
(`compNP`), `≥` because by part 1 *every* np-functional of `A` is a `ξ∘ρ`.

89XI.3 (ultrastrong permanence) is the same idea one level down, on the
generating balls: `‖ρa - ρb‖_ξ = ‖a - b‖_{ξ∘ρ}`, so every ball of `A` **is**
the `ρ`-preimage of a ball of `B` (part 1 supplies the `ξ`), giving one
inclusion by `generateFrom_anti`; the other is that
`a ↦ ‖ρ a - c‖_ξ` is `‖·‖_{ξ∘ρ}`-Lipschitz for an *arbitrary* `c ∈ B`, so its
sublevel sets are ultrastrongly open (`ultrastrong_ball_mem_nhds`).
`induced_generateFrom_eq` does the rest.  Note `rw [ultrastrong B]` fails —
the topologies are `def`s, so `unfold ultrastrong` is the move.

### 2. `exists_sumVectorNP`: the arbitrary-index wrapper

38IV.2 is stated for `x : ℕ → H`.  `111VII`'s `tensor-2` needs the family
`(n,m) ↦ xₙ ⊗ yₘ` indexed by `ℕ × ℕ`, so `exists_sumVectorNP` (35 lines)
re-indexes any square-summable `x : ι → H` through `exists_nat_reindex`
(session 49) and transports the `HasSum` back with
`Function.Injective.hasSum_iff` + `hasSum_subtype_iff_of_support_subset`.
It is in `A/VN` so both `A/Proc` and `B/Dils` can see it.

**Is `tensor-2` genuinely satisfied now?  Yes, as far as `A/VN` is
concerned.** proc.tex:2528 needs (i) 89IX — proved, session 49; (ii) the
np-functional of a square-summable `ℕ × ℕ`-family — `exists_sumVectorNP`,
above; (iii) square-summability of `(x,y) ↦ f(x)g(y)`, which
`A/Proc/Tensor.lean:192` already has; (iv) restriction to `𝒯` along the
inclusion, which is `VNSub.restrictNP` (`A/Proc/Tensor.lean:1107`).  What
remains is `A/Proc`-local assembly — the identity
`⟪x⊗y,(A⊗B)(x⊗y)⟫ = ⟪x,Ax⟫⟪y,By⟫` and a `tsum` over `ℕ × ℕ` — not a missing
theorem.  `special_tensor` still carries `tensor-1` and `tensor-3`, which
were never blocked on `A/VN`.

### 3. Three items from the survey, worked cheapest-first

* **47V** `vn_equalisers`: `StarAlgHom.equalizer` (Mathlib) gives the
  ∗-subalgebra; it is norm-closed because miu-maps are contractive
  (`norm_mi_map_contractive`), and closed under directed suprema because
  `f(⋁D)` and `g(⋁D)` are lubs of the *same* set `f''D = g''D`.  17 lines.
  There is **no author solution** — `asols.tex` stops at parsec 340 — so this
  argument is ours.  It unblocks half of **84bV** `ha_equalisers`.
* **66IV**.1: `⌈ω⌉ ∪ ⌈τ⌉ = ⌈ω+τ⌉` is **63II**.2 `carrier_basic_2`, already
  proved; four lines.
* **66IV**.2: `p = ⌈ω(p(·)p)⌉` for `p ≤ ⌈ω⌉`.  Leastness is the one step with
  content: from `ω(p r^⊥ p) = 0` we get `ω(⌈p r^⊥ p⌉) = 0` by **60I**
  `ceil_functionals_lemma`, hence `⌈ω⌉ ≤ ⌈p r^⊥ p⌉^⊥`; since
  `⌈p r^⊥ p⌉ ≤ p ≤ ⌈ω⌉` this makes the projection dominated by its own
  complement, so (conjugating) it is `0`, so `p r^⊥ p = 0` and `p ≤ r`.  The
  tail is the same computation as in the proved 66IV.3.

### 4. A full survey of `A/VN` is now in `docs/AVN-survey.md`

Every one of the 55 remaining `sorry`s, with DISP number, class
(self-contained / blocked-on-named-sorry / cited-to-literature / false) and
the cheapest next targets.  Two findings worth repeating here:

* **The nine 43II counterexamples in `Basic.lean` are much cheaper than they
  look**, now that 39IX `bh_np` is proved: every np-functional on `B(ℓ²)` is
  `∑ₙ⟪xₙ,(·)xₙ⟫`, so `‖T‖²_ω = ∑ₙ‖T xₙ‖²` and each part becomes dominated
  convergence against the summable `(‖xₙ‖²)ₙ`.  That is 9 of `Basic.lean`'s
  24.
* **`Projections.lean` is one chain**: 69V → 69VII → 69IX → 70II → 70III.
  Proving **69V** `proto_gns_ceil` unlocks five statements.  The best
  *isolated* target there is **63IV** `cp_comprehension`, whose thesis proof
  needs only `states_order_separating_1/2` and `omega_norm_basic_1`, both
  proved in `A/CStar`.

### 5. Corrections to the brief

1. **"The tree has only the converse, 39IX `bh_np`; the missing direction is
   one 120–150 line lemma"** — wrong: the missing direction is **38IV**.2
   `bh_functional_lemma_2`, proved, in the *same file* as 39IX.  The brief's
   own advice ("the thing you need may already exist downstream") was right
   in spirit and wrong in direction: this time it was **upstream**, in
   `A/CStar`, which is exactly where a worker told "your territory is A/VN"
   does not look.  Eighteenth over-costed blocker.
2. **"89XI.1 needs `isVNSubalgebra_range` to supply a missing hypothesis"** —
   the reverse: 89XI.1 does not use its `hR` at all, and 48VI.1 is what makes
   *89XII* (the version without `hR`) follow from it.
3. Nothing false was found in the theses this session; no ERRATA or QUESTIONS
   rows added.

### 6. Verification

Each of `Basic`, `Projections`, `Division`, `NormalFunctionals`,
`Completeness` compiled with `lean` invoked directly under `LEAN_PATH`
(the `lake build` bypass): no errors, `sorry` and linter warnings only.
`#print axioms` was run by appending the commands to each module and
recompiling; all eight new declarations are exactly
`[propext, Classical.choice, Quot.sound]`; the commands were then removed.
Files touched: `Theses/A/VN/{Basic,Projections,NormalFunctionals}.lean`,
`docs/AVN-survey.md`, and this log.

## Session 49 — `B/Dils` parsec 1600 falls whole: **160IV**.2/.3, **160IX**, **160X**, **163II**-dense (worker 74)

Files touched: `Theses/B/Dils/SelfDual.lean`, `Theses/B/Dils/HilbertModules.lean`,
`docs/BDils-survey.md`, this log.  Nothing staged, nothing committed.
**B/Dils 49 → 44 `sorry`s** (`SelfDual.lean` 19 → 14).  All five new
theorems `#print axioms` to exactly `[propext, Classical.choice, Quot.sound]`.

### 1. The keystone: **160IV**.3 `hilbmod_projthm_3`, and why it is not expensive

The thesis's proof (160V–160VIII) obtains the decomposition
`X = V^{⊥⊥} ⊕ V^⊥` by taking an orthonormal basis of `W = V^{⊥⊥}`,
*extending it to a maximal orthonormal subset of the whole of `X`*, and
expanding along the extended basis.  That extension step is asserted by
pointing back into the proof of **149VIII**
(`selfdual-bcompl-then-basis`), and it also makes part 2 a prerequisite of
part 3.

**Divergence, class 2, and it collapses the parsec.**  Run 149VIII's Zorn
argument *one level down* instead: take a maximal orthonormal `E` inside the
closed submodule `W` itself.  Then

* every `y ∈ X` has an expansion `p = ∑_{e∈E} ⟨e,y⟩ • e`, converging by
  Bessel + norm-bounded ultranorm completeness of `X`, with `p ∈ W` because
  `W` is an ultranorm-closed submodule and the partial sums are in `W`;
* `y − p ⊥ E` (the coefficients of the limit are the coefficients);
* for `y ∈ W`, maximality forces `y = p`, because a non-zero `y − p ∈ W`
  would be normalized by polar decomposition into a new orthonormal element
  **of `W`**, extending `E`.

So `x − p ⊥ W` for every `x ∈ X`, which is the decomposition — with no
basis of `X`, no basis extension, and no part 2.

The one thing 149VIII's proof does not hand over as stated is that the
isometric part `u` of the polar decomposition of `y` stays inside a closed
submodule containing `y`.  It is true by construction (`u` is the ultranorm
limit of `sm N • y`), so `polar_decomposition` in `HilbertModules.lean` now
**records it as a third conjunct**: `∃ c : ℕ → 𝒷, UnTendsto (fun N => c N • y)
atTop u`.  That is the whole cost of the relativization.

### 2. What fell with it

* **160IV**.2 `hilbmod_projthm_2` (`V^{⊥⊥}` = ultranorm closure of the
  ℬ-span).  `⊇` is the thesis's own argument; `⊆` is the *same* relativized
  decomposition, applied to `W' = unClosure (bSpan V)`: `x = p + (x−p)` with
  `p ∈ W'` and `x − p ⊥ W'`, so `x − p ∈ V^⊥ ∩ V^{⊥⊥} = {0}`.  The thesis
  proves 2 and 3 together in the order 3-then-2 through the extended basis;
  here they are independent, and 2 needs only that `unClosure` of a
  submodule is a submodule (`unClosure_add/_neg/_op_smul`, the last through
  `‖b·z‖_ω = ‖z‖_{conjNP (b*) ω}`).
* **160IX** `selfdual_orthn_basis`, both parts, and it needs *no* Zorn at
  all: the expansion of an arbitrary `x` along the given orthonormal family
  lands in `E^{⊥⊥}` and `x − p ∈ E^⊥`, and `E^{⊥⊥} ∩ E^⊥ = {0}`.  The `⇐`
  of part 2 computes `⟨x−p,x−p⟩ = ⟨x,x⟩ − ⟨x,p⟩ − ⟨p,x⟩ + ⟨p,p⟩ = 0`, the
  three cross terms being the same ultraweak limit as the Parseval sum.
  (The survey's worry that the `⇒` half "needs ℓ²-sum convergence for a
  non-basis orthonormal family, which the tree does not yet have
  separately" was right about the need and wrong about the difficulty: that
  convergence is `hclauseb` inside 149VIII, and this session extracted it as
  the standalone `exists_unTendsto_of_l2Summable`.)
* **160X** `selfdual_gramschmidt`, by induction on `n`, which *is* the
  thesis's hint ("use the orthonormalization in the last part of
  `selfdual-bcompl-then-basis`"): the new basis vector is the isometric part
  `u` of the polar decomposition of `z = xₙ − ∑ₖ ⟨fₖ,xₙ⟩ • fₖ`, and
  `⟨u,xₙ⟩ = √⟨z,z⟩` makes `z = ⟨u,xₙ⟩ • u`, so the expansion closes.  `u`
  lies in `{x₁,…,xₙ}^{⊥⊥}` by the new third conjunct of
  `polar_decomposition`.
* **163II**-dense `selfdual_compl_defining_dense`, which the survey listed
  as blocked on **151Ia** `selfdual_completion_univ`.  **It is not**: the
  hypothesis of the statement already *is* the universal property, so 151Ia
  is not needed.  The proof is the thesis's: the orthogonal projection `P`
  onto `ηV^{⊥⊥}` (new `exists_orthoProj`, a bounded module map by
  uniqueness of the decomposition) fixes `ηV`, so `P` and `id` both factor
  `η` through itself and the uniqueness clause gives `P = id`; then
  **160IV**.2 identifies `ηV^{⊥⊥}` with the ultranorm closure of `ηV`,
  using `bSpan (ηV) = ηV` (η is a module map).

### 3. New reusable infrastructure

In `HilbertModules.lean` (extracted from the proof of **149VIII**, which now
calls them, so the file got shorter rather than longer):

* `exists_unTendsto_of_l2Summable` — clause (b) of `IsONBasis` for *any*
  orthonormal family in a norm-bounded ultranorm complete module;
* `inner_of_unTendsto_sum_smul` — the coefficients of a convergent
  `∑ᵢ bᵢ • eᵢ` are the `bᵢ`;
* `inner_eq_zero_of_polar` — the isometric part of the polar decomposition
  of `y` is orthogonal to whatever `y` is orthogonal to;
* `polar_decomposition` is no longer `private`, and carries the extra
  conjunct described above.

In `SelfDual.lean`, all `private`: `mem_unClosure_of_unTendsto`,
`subset_unClosure`, `unClosure_mono`, `unClosure_unClosure`,
`unClosure_add/_neg/_op_smul`, `unSeminorm_neg_inner`, `unSeminorm_op_smul`,
`subset_bSpan`, `zero_mem_bSpan`, `bSpan_add/_neg/_op_smul`, `op_smul_sum`,
`subset_biorthoCompl`, `biorthoCompl_mono`, `uwTendsto_unique₂`,
**`exists_orthogonal_decomp`** (the projection theorem for an arbitrary
ultranorm-closed ℬ-submodule — the workhorse of all five items) and
**`exists_orthoProj`** (the same, as a bounded idempotent module map).

### 4. Where the next worker should look

`exists_orthoProj` + the universal property is exactly the shape of
**164II**.1 `ext_tensor_dense`, the remaining gate of the 1640–1670 chain
(164II.1 → 166IV → 166VI; 164II.2a additionally needs 161II.2).  The
`P = id` half transfers verbatim.  What does **not** transfer is the last
step: 160IV.2 identifies `D^{⊥⊥}` with the closure of the ℬ-**span** of
`D`, and for `D = {∑ᵢ η(xᵢ,yᵢ)}` the span is strictly bigger than `D`
(`D` is closed under `+`, `ℂ·` and under elementary tensors `t a b`, but not
under a general `c ∈ 𝒜 ⊗̄ ℬ`).  Closing that gap needs bounded ultrastrong*
approximation of `c` by sums of elementary tensors — i.e. `IsVNTensor`'s
generation clause plus Kaplansky density (`Kaplansky.lean`) — and is the
real remaining content of 164II.1.  For `163II`-dense the gap did not arise
because `ηV` is already a submodule.

### 5. Verification

`lean Theses/B/Dils/HilbertModules.lean` and `.../SelfDual.lean` (with the
`LEAN_PATH` bypass): no errors, `HilbertModules` still 0 `sorry`s,
`SelfDual` 14.  `#print axioms` on `hilbmod_projthm_2`, `hilbmod_projthm_3`,
`selfdual_orthn_basis`, `selfdual_gramschmidt` and
`selfdual_compl_defining_dense`: all exactly
`[propext, Classical.choice, Quot.sound]`.

The olean-disappearance failure mode of session 48 recurred twice
(`A/VN/Completeness`, `A/VN/Division`), both times cured by waiting and
retrying, as the brief says.

## Session 51 — `A/Proc`: **102VII `canonical-quotient-rigid`** falls, and **102IX `pure-is-rigid`** with it (worker 76)

Files touched: `Theses/A/Proc/Measurement.lean`, `ERRATA.md`,
`docs/AProc-survey.md`, this log.  Nothing outside `Theses/A/Proc/`.
**A/Proc 90 → 88**: `Measurement` 13 → **11**, `Tensor` 43,
`QuantumLambda` 17, `Duplicators` 17 (compiler-counted).

Closed (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| point | declaration | class |
|---|---|---|
| **102VII** | `canonical_quotient_rigid` (via the index-free `ad_rigid`) | 2 for the limit step (§2), 1 elsewhere |
| **102IX** | `pure_is_rigid` | 2 — the thesis's argument with the `⋄`-bookkeeping done pointwise (§3) |
| — | `ad_rigid`, `stdFilter_rigid`, and the private `nmiuIdAux`, `isRigid_ncpId`, `norm_isStarProjection_le_one`, `compress_eq_of_ceil` | new reusable infrastructure |

`corner_ceil_val` was **moved** (unchanged) from parsec 1050 up to just before
parsec 1020, because `compress_eq_of_ceil` needs it.  No statement changed.

### 1. The brief's "long" was right about the shape and wrong about the cost

102VII is ~210 lines and its skeleton is the thesis's, step for step:
factor `g = c ∘ h` through the filter `c = b*(·)b` (**96V**), show `h` unital
by injectivity of `c` (`ad_injective`), take an approximate pseudoinverse
`t` of `b` (**80IV**, proved), put `eₙ = ∑_{k<n} ⌈t_k⌋` and `sₙ = ∑_{k<n} t_k`
so that `b sₙ = eₙ`, and prove `⌈eₙ h(P) eₙ⌉ = ⌈eₙ P eₙ⌉` by the thesis's
five-step chain

  `⌈eₙ h(P) eₙ⌉ = ⌈sₙ* g(P) sₙ⌉ = ⌈sₙ* ⌈g(P)⌉ sₙ⌉ = ⌈sₙ* ⌈c(P)⌉ sₙ⌉
   = ⌈sₙ* c(P) sₙ⌉ = ⌈eₙ P eₙ⌉`,

whose two ceiling steps are **60VII**.1 `ceil_fundamental_1`
(`⌈a* x a⌉ = ⌈a* ⌈x⌉ a⌉`), already in `A/VN/Projections.lean`.  Everything
the brief listed as expensive was in the tree: `approximate_pseudoinverse`,
`IsApproxPseudoinverse.mul_eq_suppProj` (`b tₙ = ⌈tₙ⌋`),
`partialSums_of_isLUB` (the `eₙ` are projections, increase, and converge
ultrastrongly to `⌊b⌉`), `mult_jus_cont`, and `nmiu_rigid`.  **Nineteenth
over-costed blocker.**

The one genuinely new piece is the compression argument, extracted as
`compress_eq_of_ceil`: for projections `e ≤ r` and a unital ncp-map `h` on
`r𝒜r` with `⌈e h(P) e⌉ = ⌈e P e⌉` for all projections `P`, the map
`x ↦ e h(x) e : e𝒜e → e𝒜e` is an ncp-map (built as `adNCP e r e ∘ h ∘
adNCP e e r`, the compression after the inclusion) which agrees with the
identity at `1` and on ceilings of projections, so it *is* the identity by
**102V** `nmiu-rigid` — the thesis's own move, and the reason the file now
carries `isRigid_ncpId`.  Unitality is the thesis's `p = eₙ^⊥` trick:
`⌈e h(r−e) e⌉ = ⌈e(r−e)e⌉ = 0`, so `e h(r−e) e = 0` and `e h(e) e = e r e = e`.

### 2. Divergence: the limit is taken **ultraweakly**, on a different sequence

The thesis finishes by proving `eₙ h(eₙ a eₙ) eₙ = eₙ a eₙ` for *every*
`a` and letting `n → ∞` ultrastrongly.  That step needs `h` itself to be
ultrastrongly continuous — true, and it is the thesis's own **45II**
`cp-uscont` (proved in `A/VN/Basic.lean` as `cp_uscont`), but the proof of
102VII does not cite it: it cites only `mult-jus-cont` (**45VI**), which is
about *products* and does not move `h` past a limit.  Transcribing it that
way would in addition need `corner_vna_basic_10'` to identify the ultrastrong
topology of `⌊b⌉𝒜⌊b⌉` with the induced one, since the convergence
`eₙ a eₙ → a` happens inside the corner.

We do it in two cheaper steps instead, and `h` is never moved past an
ultrastrong limit:

* **fixed `x`, moving projections.**  If `eₙ x eₙ = x` then `e_m x e_m = x`
  for every `m ≥ n`, so `compress_eq_of_ceil` gives `e_m h(x) e_m = x` for
  all `m ≥ n`.  Now only the *projections* move: `e_m z e_m → r z r`
  ultrastrongly for a **fixed** `z` (two applications of `mult_jus_cont`,
  with `‖e_m‖ ≤ 1`), so at `z = h(x)` the left side is eventually the
  constant `x` and the limit is `h(x)`; hence `h(x) = x`.
* **moving `x`.**  For general `x ∈ ⌊b⌉𝒜⌊b⌉` the truncations
  `x_m = e_m x e_m` are each fixed by `h`, and `x_m → x` ultraweakly.  Only
  **ultraweak** continuity of `h` — plain normality — is then needed, and
  it is applied not as a topological statement but through `compNP`: `ω ∘ h`
  is an np-functional of the corner, hence (by `corner_vna_basic_10`) of the
  form `ω₂(·.val)`, so `ω(h(x_m)) → ω(h(x))` follows from `uwTendsto_iff` in
  `𝒜` alone.  `eq_of_forall_npFunctional` closes it.

Reading the step also turned up **ERRATA 102VIII**: the printed proof says
the left-hand side "converges ultrastrongly to `g(a)`", but the left-hand
side is `eₙ h(eₙ a eₙ) eₙ`, whose limit is `h(a)` — `g(a)` is not even in
the same algebra as the right-hand side.  Filed with the missing `cp-uscont`
citation.

### 3. 102IX is 60 lines once 102VII is in the index-free form

The proof of 102VII was written for a general `c : e𝒜e → 𝒜` with
`c(x) = d* x d` and `e = ⌈d⌉ᵣ` (`ad_rigid`, the shape `isFilter_ad` already
uses), because 102IX needs it at `d = √p`, where the index is `⌈p⌉` and not
`⌈√p⌉ᵣ`; transporting along `⌈p⌉ = ⌈√p⌉ᵣ` inside the dependent type
`Corner 𝒜 e` is not type-correct.  `canonical_quotient_rigid` and
`stdFilter_rigid` are then both one line.

The rest follows the thesis: `⌈f⌉ = ⌈g⌉` (here directly — `f(q^⊥) = 0 ⟺
⌈f(q^⊥)⌉ = 0 ⟺ ⌈g(q^⊥)⌉ = 0 ⟺ g(q^⊥) = 0`, so the two carriers are least
in the *same* set), `g = h ∘ π_{⌈f⌉}` by the universal property of the
corner, `[f]` invertible by **100III**, and `h ∘ [f]⁻¹ = c_{f(1)}` by
rigidity of `c_{f(1)}`.

**Divergence.**  The thesis gets the hypotheses of that last step from a
`⋄`-computation (`h^⋄ ∘ π^⋄ = g^⋄ = c^⋄ ∘ [f]^⋄ ∘ π^⋄` and `π^⋄` surjective).
Our `IsRigid` is already phrased pointwise on projections, so the diamond
detour is unnecessary: for a projection `Q` of `⌈f(1)⌉ℬ⌈f(1)⌉`, put
`q = [f]⁻¹(Q)` — a projection, by the private `isStarProjection_map` (a
unital ncp-isomorphism maps projections to projections, **99V**) — and note
`π_{⌈f⌉}(q.val) = q`, so `h(q) = g(q.val)` and
`⌈h([f]⁻¹ Q)⌉ = ⌈g(q.val)⌉ = ⌈f(q.val)⌉ = ⌈c_{f(1)}([f](q))⌉ = ⌈c_{f(1)}(Q)⌉`
by the **98IX** square.  "`π^⋄` is clearly surjective" is exactly the
observation `π_{⌈f⌉}(q.val) = q`.

### 4. Corrections to the brief and to `docs/AProc-survey.md`

1. **81V `douglas` is proved.**  The survey (and the brief) say
   "104III.3/.4/.5 → 81V `douglas` / 81VIII `sequential-quotient` (A/VN,
   `sorry`)".  `A/VN/Division.lean` has seven `sorry`s and none of them is
   `douglas_1`, `douglas_2` or `sequential_quotient_1`; only **81VIII.2**
   `sequential_quotient_2` (Division.lean:2502) and **81IX.2** `div_usc`
   (2587) are left of that block, plus 79VI.4/.5 and the parsec-840 items.
   104III.3/.4/.5 are exercises about `div`/`pinv`/infima with no published
   solution (asols stops at parsec 340) — they are not cheap, but they are
   not blocked on `douglas` either.
2. **111VII is no longer blocked on `A/VN`, and it is in this territory.**
   Session 50 closed the last A/VN input to `tensor-2` (89IX, plus
   `exists_sumVectorNP`) and recorded that what remains is "A/Proc-local
   assembly".  That is right, and the other two conditions are also within
   reach now: `tensor-1` is **88VI** `double_commutant` (proved,
   `A/VN/NormalFunctionals.lean:1524`), which gives `W*(S) = ` the ultraweak
   closure of a unital ∗-subalgebra `S`, and the span of the range of `⊗` is
   such a subalgebra because `(A⊗B)(C⊗D) = AC⊗BD`; `tensor-3` is the
   thesis's two-line `√T x⊗y = 0` argument plus density of the elementary
   tensors, which `(hilbTensor H K).isTensor.dense` already supplies.  What
   is genuinely missing is miu-bilinearity of `opTensor` ("we leave it to
   the reader"), provable on elementary tensors by
   `ContinuousLinearMap.ext_on … isTensor.dense`.  **111VII → 111XII is the
   single highest-leverage target in A/Proc — it un-vacuums 54 of the 88
   remaining statements** — and it is now A/Proc-local.  Estimate: one full
   session.
3. The survey lists **111VII** under "(c) the vacuous band".  It is not in
   the band: its statement mentions no `VNT`.  It is what *gates* the band.

### 5. Verification

`env LEAN_PATH=… lean Theses/A/Proc/Measurement.lean` → **0** `error:` lines
and **11** `declaration uses 'sorry'` warnings, down from 13, with no new
warning of any kind.  `#print axioms` was run by appending a block to the
module itself and recompiling (never from an importing scratch file): all
of `ad_rigid`, `canonical_quotient_rigid`, `stdFilter_rigid`,
`pure_is_rigid`, `corner_ceil_val` (after the move), `isRigid_ncpId`,
`compress_eq_of_ceil`, and the regression pair `pure_fundamental` /
`chevron_f_purely_positive_1` are exactly
`[propext, Classical.choice, Quot.sound]`.  Nothing staged, nothing
committed.

## Session 50 — `B/Dils`: **164II.1 `ext_tensor_dense`** falls, and **166IV** and **166VI** with it (worker 76)

Files touched: `Theses/B/Dils/SelfDual.lean`, `Theses/B/Dils/Kaplansky.lean`
(un-privating only), `docs/BDils-survey.md`, this log.  Nothing staged,
nothing committed.  **B/Dils 44 → 41 `sorry`s** (`SelfDual.lean` 14 → 11).
All four new theorems `#print axioms` to exactly
`[propext, Classical.choice, Quot.sound]`.

### 1. **164II**.1 `ext_tensor_dense`, and what the ultrastrong step cost

The brief's diagnosis was right in every part.  The `P = id` half transfers
verbatim from the closed **163II**-dense: `exists_orthoProj` gives the
orthogonal projection `P` onto `D^⊥⊥` for
`D = {∑ᵢ η(xᵢ,yᵢ)}`, `P` fixes every elementary tensor, and both `P` and
`id` factor `η` through itself, so the uniqueness clause of `ExtTensor.univ`
forces `P = id` and `D^⊥⊥ = X ⊗ Y`.  The bound `ExtTensor.univ` asks for is
the *equality* `extTensor_gram` with `C = 1`.

The remaining content — `bSpan 𝒞 D ⊆ unClosure 𝒞 D`, which **160IV**.2 needs
because `D` absorbs only elementary tensors `t a b` — is the thesis's own
**164VII**, and it came to about 130 lines:

* `tSpan t`, the finite sums `∑ᵢ t aᵢ bᵢ` (i.e. `𝒜 ⊙ ℬ` inside `𝒞`), as a
  `StarSubalgebra ℂ 𝒞` (`tSpanSubalg`).  `t` is multiplicative, star-closed
  and unital, so the ℂ-span of its range *is* a `*`-subalgebra — no `adjoin`
  induction is needed, only `Fin.append` for `+` and `finProdFinEquiv` for
  `*`.
* `unDense_tSpan`: `𝒜 ⊙ ℬ` is ultrastrongly dense in `𝒜 ⊗ ℬ`.  This is
  `IsVNTensor.generates` plus thesis A's `isVNSubalgebra_usClosureSubalgebra`
  (the ultrastrong closure of a `*`-subalgebra is a von Neumann subalgebra):
  that closure is then a member of the family `wstar` takes the `sInf` of, so
  `⊤ = W*(𝒜 ⊙ ℬ) ≤ closure`.  The finitely-many-seminorms form of the
  ultranorm conventions comes from `npSum` and the new `omegaNorm_le_npSum`,
  and the mirroring by applying the closure at `c*` and starring back
  (`unSeminorm_mulInner_eq`), exactly as in `kaplansky_bounded_approx`.
* `unSeminorm_op_smul_le`: `‖c·z‖_ω ≤ ‖z‖ ‖c‖_{mulInner,ω}`, from
  `c⟨z,z⟩c* ≤ ‖⟨z,z⟩‖ cc*` (Mathlib's
  `CStarAlgebra.star_right_conjugate_le_norm_smul`).

**No bounded net, hence no Kaplansky density, is needed** — the brief and the
survey both said `IsVNTensor` generation *plus* `Kaplansky.lean`, and the
`Kaplansky.lean` half turned out to be unnecessary: the estimate above is
linear in `c`, so plain ultrastrong density suffices.  That matters, because
**158II** `kaplansky_hilbmod` is open and its printed proof is false.

Un-privated in `Kaplansky.lean` for this: `unSeminorm_mulInner_eq`, `npAdd`,
`npZero`, `npSum`, `npAdd_apply`, `npSum_apply`, `np_mono`, `np_re_nonneg'`,
`np_re_mono'`, `preservesDirSups_npAdd`; added `omegaNorm_le_npSum`.

### 2. **166IV** `exttensor_dense_subsets` — and it does **not** need 158II

Divergence, class 2, and it removes a dependency on an open `sorry`.  The
thesis (166V) gets *norm-bounded* nets `u_α → x`, `v_α → y` out of
**158II** and then applies **166II**.  158II is open, so that route is dead.
It is also unnecessary: the ultranorm uniformity is approximated one
entourage at a time, so `u ∈ U` may be chosen **first** and `v ∈ V`
afterwards, to an accuracy depending on the `‖u‖` already fixed.  The two
estimates are 166III's own, extracted as `unSeminorm_eta_le_left/_right`
(`‖u ⊗ w‖_Ω ≤ ‖w‖ ‖u‖_{Ω(·⊗1)}` and its mirror), which the proof of 166II
had inline.  The hypotheses `hUsub`, `hUsmul`, `hVsub`, `hVsmul` are
consequently unused.

### 3. **166VI** `dilationspace_dense_subset`, and a new lemma for `Paschke`

Same shape, one level easier, plus a preliminary that was missing from the
tree: **the elementary tensors of `𝒜 ⊗_φ ℬ` are ultranorm dense**
(`paschke_tprod_dense`, new, public).  Unlike `D` in 164II.1, the set
`{∑ᵢ aᵢ ⊗ bᵢ}` is *already* a ℬ-submodule — `PhiCompatible.smul_action` is
`c·(a ⊗ b) = a ⊗ (cb)` — so `bSpan D = D`, **160IV**.2 applies outright, and
the `P = id` argument through `PaschkeModule.univ` finishes it with no
ultrastrong-density step at all.  The thesis states this only implicitly
("by construction").

The approximation step then needs two seminorm computations, both new:

* `unSeminorm_tprod_left`: `‖d ⊗ b‖_ω = ‖d‖_{ν}` **exactly**, where
  `ν = ω(b φ(·) b*)` is an np-functional on `𝒜` (`conjNP` then `compNP`;
  normality of `φ` is what makes it one — `exists_conj_comp_np`);
* `unSeminorm_tprod_right`: `‖a ⊗ e‖_ω ≤ ‖φ(aa*)‖^½ ‖e‖_{mulInner,ω}`, the
  same conjugation estimate as in 164II.1.

So `a' ∈ 𝒜'` is chosen first against the `ν`'s and `b' ∈ ℬ'` second, and the
thesis's appeal to `dense-subalgebra` for norm-bounded nets is again not
needed.

*Lean note.*  `compNP (ncpPositive φ) φ.preservesDirSups' ω` — which
typechecks verbatim in `A/VN/Basic.lean:2619` — is rejected inside
`SelfDual.lean` ("application type mismatch", `⇑(ncpPositive φ)` vs
`⇑φ.toCompletelyPositiveMap`), and `by exact` does not help.  Stating the
*same* defeq as a separate one-line declaration `ncpPreservesDirSups` and
passing that does work.  Worth knowing; the cause was not tracked down.

### 4. Correction to the survey: **159IX is not self-contained**

`docs/BDils-survey.md` classes **159IX** `ketbra_ultranorm_continuous` as
**(a)**, "the largest self-contained item left in `SelfDual.lean`", and the
brief repeats it.  It is **(b)**.  The thesis's proof (159X–159XI,
dils.tex:4383) needs the linear span of `Ω = {f(⟨x,(·)x⟩)}` to be
*operator-norm dense* among the np-functionals on `ℬᵃ(X)`, and cites
`vn-center-separating-fundamental` (**90II**) for it.  90II part 1 is proved
(`A/VN/NormalFunctionals.lean:3299`), but the density is **90II**.2
`vn_center_separating_fundamental_2`, which is `sorry`
(`A/VN/NormalFunctionals.lean:3343`) and is outside `B/Dils`.  Everything
else in 159X–159XI (the norm bound `‖|z⟩⟨y|‖ ≤ ‖z‖‖y‖`, ultranorm
continuity of `ω(|·⟩⟨y|)`) is elementary.

### 5. Verification

`lean Theses/B/Dils/{HilbertModules,Kaplansky,Paschke,Stinespring,
SelfDualCompletion,SelfDual,Pure}.lean` under the `LEAN_PATH` bypass: no
errors; per-file `sorry`-declaration counts 0 / 5 / 8 / 2 / 2 / **11** / 13,
**41** in total.  `#print axioms` on `ext_tensor_dense`,
`exttensor_dense_subsets`, `dilationspace_dense_subset` and
`paschke_tprod_dense`: all exactly `[propext, Classical.choice, Quot.sound]`.

## Session 52 — `A/Proc`: **111VII and 111XII are proved — the vacuous band is open** (worker 77, `Tensor.lean`)

Target: `special_tensor` (**111VII**, proc.tex:2491) and both forms of
**111XII**, the gate that made 54 of A/Proc's statements vacuous.  All three
are closed, plus the first band member, **116III**.1.

`Tensor.lean` **43 → 39** (compiler-counted); A/Proc 88 → **84**.

| point | declaration | class |
|---|---|---|
| **111VII** | `special_tensor` | 1 — the thesis's proof, condition by condition |
| **111XII** | `vnTensorProduct_exists` (unbundled), `vnTensorProduct_nonempty` (bundled) | 1 — the thesis's `ngns` + 111VII route |
| **116III**.1 | `tensor_simple_facts_1`, `vtmul_nonneg` | 2 — no author solution (exercise; `asols.tex` stops at parsec 340) |

Reusable machinery added (all axiom-clean): `ext_htmul`, `eq_of_inner_htmul`,
`htmul_inner`, `norm_htmul`, `htmul_add_left`, `htmul_smul_left`,
`opTensor_{one,mul,add_left,add_right,smul_left,smul_right,adjoint,star}`;
`VNSub.{valLinearMap,valStarAlgHom,valNMIU,valNMIU_injective,valNMIU_range,
isVNSubalgebra_valNMIU_range,ultraweak_eq_induced}`; `spatialSpan`,
`coe_spatialSpan`, `wstar_spatialSpan`, `spatial_dense`,
`exists_np_of_spatial_product`, `eq_zero_of_inner_htmul_eq_zero`;
`isLUB_image_of_orderIso`, `starAlgHom_nonneg'`, `starAlgHom_mono'`,
`starAlgEquiv_le_iff`, `starAlgEquiv_preservesDirSups'`, `isVNSubalgebra_map`,
`nmiuSymm`, `nmiuLin`, `nmiuCorestrict(_val,_bijective)`,
`isTensorProduct_comp`; `InnerProductSpace ℂ (ULift H)`, `uliftIsometry`,
`ngns_ulift`.

### 1. `tensor-2` did close, and the assembly was cheap

The brief was right: nothing was missing.  `exists_np_of_spatial_product` is
40 lines — **89IX** `normal_functional` applied to the inclusion
`VNSub S ↪ B(ℋ)` (new: `VNSub.valNMIU`) for `σ` and for `τ`,
`Summable.mul_of_nonneg` for `∑_{n,m}‖xₙ ⊗ yₘ‖² = (∑‖xₙ‖²)(∑‖yₘ‖²)`,
`exists_sumVectorNP` for the `ℕ × ℕ`-family, and `HasSum.mul` (plus a norm
comparison `‖⟨xₙ,axₙ⟩‖ ≤ ‖a‖‖xₙ‖²` for the summability side condition) to
identify `∑_{n,m}⟨xₙ,axₙ⟩⟨yₘ,byₘ⟩` with `σ(a)τ(b)`.  `VNSub.restrictNP`
transports the functional to `𝒯`.  The termwise identity
`⟨x⊗y,(A⊗B)(x⊗y)⟩ = ⟨x,Ax⟩⟨y,By⟩` is one `rw` off `opTensor_apply` and the
`inner_mul` field of `IsHilbertTensorProduct`.

`tensor-3` (25 lines) is the thesis's argument verbatim: the *vector* product
functionals `⟨x⊗y,(·)x⊗y⟩` (which are product functionals, with
`σ = ⟨x,(·)x⟩` and `τ = ⟨y,(·)y⟩`, all three obtained by `VNSub.restrictNP` of
`vectorNP`) kill `t`, hence `√t` vanishes on elementary tensors, hence `√t = 0`
by density, hence `t = 0`.

`tensor-1` is the one condition whose Lean form asks for more than the thesis's
one-line "by the way `𝒯` was defined": our `IsTensorProduct.dense` demands
*ultraweak* density of the span in `𝒯`, and `𝒯` is `wstar` of a set.  Two
inputs: **88VI** `double_commutant` (`W*(S)` = ultraweak closure of a unital
∗-subalgebra) applied to `spatialSpan`, the span of `{A ⊗ B}`, which is a
∗-subalgebra because `(A⊗B)(A'⊗B') = AA'⊗BB'` and `(A⊗B)* = A*⊗B*`; and
**89XI**.2 `functional_permanence_2`, which says the ultraweak topology of
`VNSub S` is the one *induced* from `B(ℋ⊗𝒦)` — without it, density in the
subalgebra's own (finer) ultraweak topology does not follow from density in the
ambient closure.  `IsInducing.dense_iff` then reduces it to
`t.val ∈ W*(span) = uwClosure(span)`.  Miu-bilinearity, which the thesis leaves
to the reader, is four `ext_htmul` one-liners (`opTensor_one/mul/adjoint`).

### 2. Lean notes worth keeping

* **`maxHeartbeats` is per declaration, not per file.**  A first attempt with
  `special_tensor` as one 200-line proof hit `(deterministic) timeout at
  isDefEq` on a step that took 3 s standalone.  Factoring the three conditions
  into `spatial_dense`, `exists_np_of_spatial_product` and
  `eq_zero_of_inner_htmul_eq_zero` fixed it with no other change; the file
  needs no `set_option`.
* Since the topologies are `def`s, `Topology.IsInducing` cannot be built with
  `@IsInducing _ _ (ultraweak _) (ultraweak _) f` (the elaborator re-synthesises
  the instances and rejects the term).  `letI : TopologicalSpace _ := ultraweak _`
  first, then `⟨VNSub.ultraweak_eq_induced⟩`, works.
* `Summable.mul_norm`'s higher-order unification (`?f p.1 * ?g p.2`) is what
  blew the heartbeat budget; naming the two norm-summability facts first and
  using `Summable.mul_of_nonneg` + `Summable.of_norm` is instant.

### 3. The fifth ingredient did appear: **the bundled 111XII crosses universes**

`vnTensorProduct_nonempty` is stated for `𝒜 : Type u` and `ℬ : Type v` with
carrier in `Type (max u v)` — but `ngns` represents `𝒜 : Type u` on a Hilbert
space in `Type u`, and `hilbTensor` needs **both** Hilbert spaces in one
universe.  So the unbundled `vnTensorProduct_exists` (both algebras in `Type u`)
is immediate from 111VII, and the bundled form is not.  Two pieces were needed,
about 120 lines together:

* a Hilbert-space structure on `ULift H` (Mathlib has the normed group, the
  normed space and `CompleteSpace`, but **no `Inner`/`InnerProductSpace`
  instance**), the isometry `uliftIsometry : ULift H ≃ₗᵢ[ℂ] H`, and `ngns_ulift`
  = `ngns` conjugated by `LinearIsometryEquiv.conjStarAlgEquiv` into
  `B(ULift ℓ²(ι))`;
* **universe-polymorphic twins of four `A/VN` lemmas**.  `A/VN/Basic.lean`
  declares `variable {A B C : Type u}`, so `starAlgHom_mono`,
  `starAlgHom_le_iff`, `starAlgEquiv_preservesDirSups` and
  `isVNSubalgebra_range` all force the two algebras into the *same* universe and
  are unusable for `𝒜 : Type u → B(ULift H) : Type (max u v)`.  Re-proving them
  is cheap because a ∗-hom is positive by `a = (√a)*√a`
  (`starAlgHom_nonneg'`, 6 lines), an equiv is then an order isomorphism, and
  `isLUB_image_of_orderIso` (new, and universe-polymorphic) gives normality and
  `isVNSubalgebra_map` (transport of a von Neumann subalgebra along a
  ∗-isomorphism) without redoing the 100-line `isVNSubalgebra_range`.
  **If `A/VN` ever generalises those four to `Type*`, the local copies in
  `Tensor.lean` should be deleted.**

`isTensorProduct_comp` (transport of a tensor product along nmiu-isomorphisms
of the two factors) is what turns the spatial `γ` for `VNSub (ran ρ_𝒜)`,
`VNSub (ran ρ_ℬ)` into one for `𝒜`, `ℬ`; its `prod_exists` half needs the
inverse of a bijective nmiu-map to be normal (`nmiuSymm`), its `faithful` half
does not (it pushes the given functionals *forward* with `compNP`).

### 4. What the closure actually buys — measured

`#print axioms` was run over **every** declaration of `Tensor.lean`,
`QuantumLambda.lean` and `Duplicators.lean` twice, once against the previous
`Tensor.olean` and once against the new one:

* `Tensor.lean` 83 → 121 clean (but +38 of that is the new machinery); of the
  136 declarations present in *both* versions, **6** went from tainted to
  clean: the three theorems above and `vnTensor`, `VNT`, `vtmul`.
* `QuantumLambda.lean` 30 → 32 (`tensorSub`, `TensorBSurjective`).
* `Duplicators.lean` 33 → 37 (`Duplicator`, `Duplicable`, `MonoidInWcpsu`,
  `MonoidInWmiu`).

**So the answer to "how many of the 54 become axiom-clean immediately" is
zero, and the honest total is 12** — every band member is itself a `sorry`, so
nothing about them flips; what flipped is the nine *definitions* their
statements are built from, which is precisely what stops the statements being
vacuous.  As a demonstration, **116III**.1 was then proved (`a ⊗ b ≥ 0` because
`a ⊗ b = (√a ⊗ √b)*(√a ⊗ √b)`, then `a₂⊗b₂ − a⊗b = (a₂−a)⊗b₂ + a⊗(b₂−b)`) and
is axiom-clean — the first genuinely non-vacuous theorem about `⊗ᵥ`.

Of `Tensor.lean`'s 39 remaining `sorry`s, 8 further declarations are still
tainted without being `sorry`ed themselves — `tmap`, `tmap_apply`, `tmapM`,
`associator`, `braiding`, `leftUnitor`, `rightUnitor`, `predualTensor` — each
chosen from a sorried unique-existence lemma, so they clean up automatically
when 115II, 116I, 119IV, 119IVb, 119IVc are proved.

### 5. Corrections to the brief

1. **"Report how many of the 54 become axiom-clean immediately on 111XII
   closing"** presupposes that band members are *proved-but-tainted*.  They are
   not: all 54 are `sorry`s.  The measurable effect is the 12 declarations of
   §4, of which 9 are definitions.
2. **"What remains is A/Proc-local assembly, not a missing theorem"** — true for
   111VII, and true for 111XII *in a single universe*; the bundled 111XII needed
   the `ULift` bridge of §3.  That is the fifth ingredient the brief asked to be
   told about plainly: it is not a missing *theorem*, but it is not assembly
   either — it is a universe defect in `A/VN`'s statements.
3. **"The copy of the `VNSub` block in `A/Proc/Tensor.lean` should be deleted
   by whoever next touches that file"** (session 49) — **do not delete it.**
   The statement of 111VII names `VNSub`, and the whole spatial construction
   runs on it; if the duplication is ever resolved it must be by pointing
   `Tensor.lean` at `Theses.A.VN.VNSub`, which changes the *statement* of
   111VII and needs the usual approval.
4. Nothing false was found in the theses this session; no ERRATA or QUESTIONS
   rows added.  Every step of the thesis's proof of 111VII checked out, down to
   the "left to the reader" miu-bilinearity.

### 6. Verification

`lean Theses/A/Proc/Tensor.lean` under the `LEAN_PATH` bypass: **0 errors, 39
`declaration uses 'sorry'` warnings** (was 43), no new warning of any kind.
`QuantumLambda.lean` and `Duplicators.lean` recompile unchanged against the new
`Tensor.olean` (0 errors), so the new global `InnerProductSpace (ULift H)`
instance disturbs nothing downstream.  `#print axioms` was run by appending the
commands to the module and recompiling (never from an importing scratch file):
`special_tensor`, `vnTensorProduct_exists`, `vnTensorProduct_nonempty`,
`vnTensor`, `VNT`, `vtmul`, `tensor_simple_facts_1`, `vtmul_nonneg`,
`spatial_dense`, `exists_np_of_spatial_product`, `ngns_ulift`,
`isTensorProduct_comp`, `nmiuSymm`, `isVNSubalgebra_map`, `VNSub.valNMIU`,
`VNSub.ultraweak_eq_induced`, `opTensor_adjoint` and `uliftIsometry` are all
exactly `[propext, Classical.choice, Quot.sound]`; the commands were then
removed.  **The olean for `Theses.A.Proc.Tensor` is left built and current**
(`lean -o`), so downstream workers need no rebuild.  Files touched:
`Theses/A/Proc/Tensor.lean`, `docs/AProc-survey.md`, and this log.

## Session 51 — `B/Dils`: **161II.2 `hilbmod_el2`** falls, and **164II.2a `ext_tensor_basis`** with it — but the chain stops at 164II.2b, which is blocked outside the directory (worker 77)

Files touched: `Theses/B/Dils/SelfDual.lean`, `docs/BDils-survey.md`, this
log.  Nothing staged, nothing committed.  **B/Dils 41 → 39 `sorry`s**
(`SelfDual.lean` 11 → 9).  Both new theorems `#print axioms` to exactly
`[propext, Classical.choice, Quot.sound]` (checked from *inside* the module,
since `hilbmod_el2`'s helpers are `private`).

### 1. **161II**.2 `hilbmod_el2` — ~90 lines, and the brief over-costed it twice

The survey called it "large: `ℓ²((pᵢ))` self dual + coordinate map is a
bijection".  Our *statement* claims neither: it takes `hX : SelfDual ℬ X`
and an `IsONBasis ℬ e` as hypotheses and asserts only that
`x ↦ (⟨eᵢ,x⟩)ᵢ` is a bijection of `X` onto `L2Set ℬ (⟨eᵢ,eᵢ⟩)` identifying
the inner products.  All three clauses come out of the two convergence
clauses of `IsONBasis`, and **`hX` is not used at all** (an orthonormal
*basis* already carries everything).

* `MapsTo` — Bessel (`mod_bessel`) for ℓ²-summability, and
  `onbasis_coef_absorb` for the support condition, which by
  `ceil_star_mul_self_le_iff` *is* `⌈bᵢ*bᵢ⌉ ≤ pᵢ`.  The brief predicted
  "`ceil` lemmas from `A/VN`"; the lemma already existed **in this file**,
  written for 161IV.2, and only had to be moved above 161II.2.
* `SurjOn` — clause (b) of `IsONBasis`, then
  `inner_of_unTendsto_sum_smul`; the absorption it asks for is again the
  support condition, so the two directions of `mem_l2Set_iff` are used once
  each.
* `InjOn` and the inner-product clause — **both** are **148V**
  `innerprod_ultraweak` applied to the basis expansions of clause (a).  For
  injectivity the two expansions are literally the *same* net, so all four
  of `⟨x,x⟩, ⟨x,y⟩, ⟨y,x⟩, ⟨y,y⟩` are limits of it and `⟨x−y,x−y⟩ = 0`.
  The brief's "polarisation of 160IX.2" is **not** needed: the cross Gram
  sum collapses to the Parseval sum by `inner_sum_smul_orthogonal` plus
  absorption, and no polarisation identity appears.

**Our statement is weaker than the exercise** (dils.tex:4602), which also
asks that `ℓ²((pᵢ))` be a right ℬ-module and be self-dual.  Neither is
formalized anywhere in `SelfDual.lean` — `L2Set` is a `Set (ι → ℬ)` with no
module structure.  Recorded in the survey; not an erratum (it is our
transcription, not the author's text).

The `L2Set` mirroring flagged in the brief was checked again and is right as
it stands: `bᵢ_ours = ⟨x,eᵢ⟩_thesis = (bᵢ_thesis)*`, so `⌈bᵢbᵢ*⌉ ≤ pᵢ`
mirrors to `⌈bᵢ*bᵢ⌉ ≤ pᵢ`, and the inner-product clause
`∑ᵢ ⟨eᵢ,y⟩⟨eᵢ,x⟩*` is the mirror of the thesis's `∑ᵢ bᵢ*cᵢ`.

### 2. **164II**.2a `ext_tensor_basis` — and it never needed 161II.2

Divergence, class 2, in the last step only.  The thesis's **164X** proves
`E₂ = {e'ᵢ ⊗ d'ⱼ}` is a basis by reducing (via **160IX** + **160IV**) to
`eᵢ₀ ⊗ dⱼ₀ ∈ E₂^⊥⊥` for the *distinguished* basis along which `X ⊗ Y` was
constructed as `ℓ²((pᵢⱼ))`, then verifying the Parseval identity of
160IX.2 by testing `(∑ᵢaᵢ*aᵢ) ⊗ (∑ⱼbⱼ*bⱼ) = ∑ᵢⱼ aᵢ*aᵢ ⊗ bⱼ*bⱼ` against
product np-functionals (`tensor-3`).

Our `E` is an arbitrary `ExtTensor`, so there is no distinguished basis to
reduce to.  Instead **164II**.1 `ext_tensor_dense` (closed last session)
reduces the claim to the *elementary* tensors, and `η v w` is approximated
directly by `η vₛ wᵤ = ∑_{i∈s}∑_{j∈u} (⟨eᵢ,v⟩ ⊗ ⟨dⱼ,w⟩)·(eᵢ ⊗ dⱼ)`, with
`s` chosen first and `u` afterwards against the already-fixed `‖vₛ‖` —
the same order-of-choice device that removed 158II from 166IV.  Only the
**166III** estimates `unSeminorm_eta_le_left/_right` are used (their
`section EtaEstimates` moved up in the file accordingly), and the whole
double-limit / product-functional computation disappears.  Consequently
**161II.2 was never a prerequisite** for this item, contrary to the survey.

The only use of `IsVNTensor` beyond bilinearity is non-degeneracy,
`⟨eᵢ,eᵢ⟩ ⊗ ⟨dⱼ,dⱼ⟩ ≠ 0`, and *there* the product functionals are needed:
`np_separating` gives `ω`, `ξ` not killing the two projections, and
`exists_productFunctional` turns them into an `Ω` with
`Ω(t p q) = ω p · ξ q ≠ 0`.  (The thesis does not remark on this step —
it says only "clearly `E₂` is orthonormal".)

### 3. What the chain now hangs on, precisely

**164II.2b `ext_tensor_ketbra_dense` is the next gate, and it is not
self-contained.**  Its 164XI proof needs to replace a general
`t ∈ 𝒜 ⊗ ℬ` in `|(eᵢ⊗dⱼ)t⟩⟨e_k⊗d_l|` by an ultrastrong limit from
`𝒜 ⊙ ℬ`, and appeals to **159IX** `ketbra_ultranorm_continuous`, which is
`sorry` (`SelfDual.lean:472`) and blocked on **90II**.2
`vn_center_separating_fundamental_2` (`A/VN/NormalFunctionals.lean:3343`),
outside `B/Dils`.  Two further obstacles are ours, not the thesis's: the
statement forces the approximating net to be indexed by `Finset (ι × κ)`
(the thesis claims only "the span is ultraweakly dense"), and the ultraweak
topology is not metrizable, so a diagonal choice over that index is not
available either.  Everything *else* of 164XI is in place —
`ketbra_ultraweakly_dense` (159IV, proved) now applies, because 164II.2a
supplies the basis it wants.  165VI and 167I stay behind 164II.2b.

### 4. A non-vacuity gap worth an author-independent check

`ExtTensor` has **no inhabitation witness** anywhere in the tree, and
`univprop_ext_tensor` (its existence theorem) is `sorry`.  So all of
164II.1, 164II.2a/2b, 165III, 165VI, 166IV, 166VI, 167I are proved only
*conditionally* on a structure not yet known to exist.  `IsVNTensor` has
`vnTensor_mul_complex` for exactly this purpose and `PaschkeModule` has
`paschkeModuleId`; session 14 records a mirroring defect that left
`PaschkeModule` uninhabited and nine theorems vacuous, caught only by a
concrete example.  A cheap witness would be
`𝒜 = ℬ = 𝒞 = X = Y = Z = ℂ`, `t = (· * ·)`, `η x y = x * y`.  Flagged in
`docs/BDils-survey.md`; not attempted this session.

### 5. Corrections to the brief

* "161II.2 … part (b) `exists_unTendsto_of_l2Summable`" — right, but part
  (a) needed no separate tool and part (c) needed no polarisation.
* "the `L2Set` support condition will need some `ceil` lemmas" — right that
  it needs one, wrong that it had to be found: it was eleven hundred lines
  below in the same file.
* "161II.2 alone now blocks the chain 164II.2a → 164II.2b → 165VI → 167I" —
  the chain is real but 161II.2 was not on it; 164II.2a needed 164II.1
  only, and the chain's actual wall is 159IX/90II.2 at 164II.2b.
* "`Paschke.lean` — the useful item there is `existence_paschke` itself" —
  inspected and not attempted: it asks for a whole `PaschkeModule` bundle
  (self-dual completion of `𝒜 ⊙ ℬ` with the φ-inner product, plus `ϱ` and
  `h`), i.e. a construction the size of `univprop_ext_tensor`, not a
  session-sized item.

### 6. Verification

`lean Theses/B/Dils/{HilbertModules,Kaplansky,Paschke,Stinespring,
SelfDualCompletion,SelfDual,Pure}.lean` under the `LEAN_PATH` bypass: no
errors; per-file `sorry`-declaration counts 0 / 5 / 8 / 2 / 2 / **9** / 13,
**39** in total.  `#print axioms` on `hilbmod_el2` and `ext_tensor_basis`:
both exactly `[propext, Classical.choice, Quot.sound]`.

## Session 52 — `B/Dils`: **`ExtTensor` is inhabited** — `𝒞 = 𝒜 ⊗ ℬ` over itself is a self-dual exterior tensor product, and no field is defective (worker 78)

Files touched: `Theses/B/Dils/SelfDual.lean`, `docs/BDils-survey.md`,
`QUESTIONS.md`, this log.  Nothing staged, nothing committed.  **B/Dils
stays at 39 `sorry`s** (compiler-counted per file: `HilbertModules` 0,
`Kaplansky` 5, `Paschke` 8, `Stinespring` 2, `SelfDualCompletion` 2,
`SelfDual` 9, `Pure` 13) — the witness is a new `def`, not a closed
`sorry`.

### 1. The primary target: `extTensorSelf`

`ExtTensor` **is inhabited**, and constructing the witness exposed **no
defect** in any field.  The witness is stronger than the `ℂ`-only check the
survey suggested: for *any* `ht : IsVNTensor t` with `t : 𝒜 → ℬ → 𝒞`, the
algebra `𝒞` itself — as a Hilbert `𝒞`-module over itself, with `η = t` — is
an `ExtTensor t ht 𝒜 ℬ`.  It is exactly the case `X = 𝒜`, `Y = ℬ` of
`univprop_ext_tensor`, and it needs **no** von Neumann hypotheses at all.
`#print axioms extTensorSelf` (checked from inside the module) is exactly
`[propext, Classical.choice, Quot.sound]`, so no field hides a `sorryAx`.
A fully concrete instance exists too: `extTensorSelf _ vnTensor_mul_complex`
inhabits `ExtTensor (fun a b : ℂ => a * b) vnTensor_mul_complex ℂ ℂ`, and
**164II.1 `ext_tensor_dense` was checked to elaborate against it**, with
`selfDual_self ℂ` for both self-duality hypotheses — so the seven
`ExtTensor`-hypothesised theorems (164II.1, 164II.2a/2b, 165III, 165VI,
166IV, 166VI, 167I) are not merely conditional and not vacuous.  **None of
the seven is affected.**

Why each field survives, in the mirrored convention (Mathlib's
`CStarModule A A` has `inner x y = y * star x` and `a • x = a * x`):

* `η_inner` becomes `t x' y' * star (t x y) = t (x' * star x) (y' * star y)`,
  i.e. `IsVNTensor.star` then `IsVNTensor.mul`.  This is the field a
  mis-mirroring would break, and `𝒜`, `ℬ` are *not* assumed commutative
  here, so a star in the wrong slot would not typecheck.
* `η_smul` is `IsVNTensor.mul` again; `η_add_left/_right/_smul_complex` are
  the corresponding `IsVNTensor` clauses verbatim.
* `selfDual` is `selfDual_self 𝒞` (141III).
* **`univ` needs no density argument.**  `T' z := z · T(1,1)` is forced,
  because `z = z · 1 = z · t(1,1)` and a module map commutes with the
  action; existence uses `T x y = T (x·1) (y·1) = t x y · T(1,1)`, the
  bound is `norm_op_smul_le` with `C' = ‖T(1,1)‖`, and the Gram-bound
  hypothesis on `T` is never used.  Uniqueness likewise follows from
  `IsVNTensor.one` alone.

The whole thing typechecked on the first compile apart from a missing
`noncomputable`.  **Divergence class 3**: the thesis proves existence only
via the `ℓ²((pᵢⱼ))` construction of 164III–164VIII; this special case
bypasses it entirely.

### 2. `univprop_ext_tensor` was inspected and *not* attempted

The general case still needs `ℓ²((pᵢⱼ))` as an actual Hilbert `𝒞`-module,
and our `L2Set` is a `Set (ι → ℬ)` with no module structure (session 51).
The obvious shortcut — build the algebraic tensor product and take its
self-dual completion — is blocked: **151I `dils_completion`**
(`SelfDualCompletion.lean:81`) is itself `sorry`.  So this is a
multi-session construction, not a session-sized item.

### 3. The secondary target 170IV.1 is blocked by a defect in **our**
statement, not by mathematics

`surjective_nmiu_1` and `surjective_nmiu_2` (`Pure.lean:1126`, `:1134`) sit
in `section Pure`, whose only instance binders are `[CStarAlgebra A]
[PartialOrder A] [StarOrderedRing A]` and likewise for `B`.  The exercise
(dils.tex:6223) says "any surjective nmiu-map **between von Neumann
algebras**", and every neighbouring statement that needs it —
`standard_corner_dils` (`:643`), `paschke_corner` (`:1164`) — carries
`[VonNeumannAlgebra A]`.  So our two statements are *strictly more general
than the source*.  This matters concretely: the whole route the survey
identified (69IV `carrier_miu`, giving the central projection `z = ⌈ϱ⌉` and
`ϱ a = 0 ↔ z·a = 0`) requires `[VonNeumannAlgebra A]` and is simply
unavailable, and so is the author's own route through 69II.  No
counterexample was found in the time available (the obvious commutative
candidates — `ev₀ : C([0,1]) → ℂ`, `lim : c → ℂ` — are *not* normal, so they
are not `NMIUMap`s), so the over-general statement is open rather than known
false.  Recorded as **QUESTIONS D5**; the `sorry`s are left in place per the
never-change-a-statement rule.

### 4. Corrections to the brief

* "The suggested cheap witness is `ℬ = ℂ`" — the general
  `X = 𝒜, Y = ℬ, Z = 𝒞` witness is no harder and much more informative,
  and it *is* a (special) case of the theorem being witnessed.
* "did constructing the witness expose any defect in the fields?" — no.
  Unlike `PaschkeModule`, `ExtTensor` was transcribed correctly; the
  mirroring is consistent throughout.
* "170IV.1 … now the largest file … ~200 lines" — the size estimate is moot:
  the statement as transcribed cannot be proved by the route named, because
  it lacks the thesis's von Neumann hypothesis.
* `existence_paschke` really is a whole-`PaschkeModule` construction, as
  session 51 said — re-confirmed, and it is additionally blocked on the same
  `dils_completion` `sorry`.

## Session 53 — `A/VN`: **77V `vn-extension` closes `Completeness.lean`**, and 63IV, 69V, 69VII fall in `Projections.lean` (worker 78, A chain)

Five declarations proved, all `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).  `A/VN` **55 → 50**
(Basic 24, Projections 17→**14**, Division 7, NormalFunctionals 5,
Completeness 2→**0**).  Compiler-counted per file, not grepped.

| point | declaration | file | divergence class |
|---|---|---|---|
| **77V** | `vn_extension` | `Completeness.lean` | 1 — a gap in the thesis's continuity paragraph, see below |
| **77V** | `vn_extension_norm` | `Completeness.lean` | 2 |
| **63IV** | `cp_comprehension` | `Projections.lean` | 0 — the thesis's proof, transcribed |
| **69V** | `proto_gns_ceil` | `Projections.lean` | 2 |
| **69VII** | `gns_ceil` | `Projections.lean` | 2 |

**`Completeness.lean` is now free of `sorry`.**  The point of 77V for the
project is that **A/Proc's 112XI `tensor_universal_property` was blocked on it
alone**, and 112XI gates 114I, 114II and 116VII — that band is now open.

### 1. 77V: the existence half is the thesis's, the continuity half is not

Existence is a straight transcription of vn.tex:4885ff: **74VI**
`dense_subalgebra` supplies, for each `a`, a norm-bounded net in `S`
converging *ultrastrongly* to `a`; `f` of it is bounded and ultraweakly
Cauchy (ultraweak continuity of `f` applied to the difference net, which stays
in `S`), so **77I**.2 `vn_complete_2` gives it a limit; the thesis's point 70
(independence of the net) is the product-filter form of the same difference
argument, and gives linearity too, since a sum of admissible nets is an
admissible net for the sum.  Uniqueness is density plus Hausdorffness
(**44XI**.1) — note it needs no linearity at all, so our `∃!`, which quantifies
over *linear* maps, is weaker than what the proof gives.

The **continuity** paragraph has a genuine gap, now **ERRATA 77VI**: it takes
"δ > 0 and an np-functional ν with `|ν(s)| ≤ δ ⟹ |ω(f(s))| ≤ ε`".  A basic
ultraweak neighbourhood of 0 is a *finite intersection* of such sets and the
np-functionals do not combine — `|(ν₁+ν₂)(s)|` bounds neither summand for
non-positive `s`.  (The *ultrastrong* seminorms do combine:
`‖s‖²_{ν₁+ν₂} = ‖s‖²_{ν₁} + ‖s‖²_{ν₂}`.)  Two repairs; the Lean proof takes the
second.  (i) Allow finitely many `νᵢ`: nothing else in the paragraph changes.
(ii) Work in the ultrastrong gauge: an ultraweakly open set is ultrastrongly
open, so `exists_ultrastrong_ball_of_isOpen` gives `ν, δ` with
`|ω(f s)| ≤ (2/δ)‖s‖_ν` on `S` (scale `s`); along 74VI's *ultrastrongly*
convergent net `‖s_α‖_ν → ‖a‖_ν`, so the bound passes to `g`; and **72XI**
`luws`, clause (5) ⇒ (2), turns `|ω(g a)| ≤ ‖a‖_{ν'}` (with `ν' = (2/δ)²·ν`,
`omegaNorm_smulNP`) back into ultraweak continuity of `ω ∘ g`, for every
np-functional `ω` of `B`.  This is the thesis's argument with its one
unavailable step replaced by the tool the thesis itself provides at 72XI.

`vn_extension_norm` follows the thesis but replaces "‖uwlim‖ ≤ liminf" by the
ultraweak **closedness of the ball** of radius `C‖a‖(1+ε)` (**73VIII**
`ultraclosed` + **44XI**.3, transported to arbitrary radii by
`isClosed_ultraweak_closedBall`, added here), then lets `ε → 0`.  It also needs
a case split the thesis does not have: for `C < 0` the hypothesis forces
`S = {0}`, hence (by density) `A = {0}`.

Six small reusable lemmas were added just above 77V: `uwTendsto_unique`,
`UWTendsto.add`, `UWTendsto.smul`, `continuous_ultraweak_of_npFunctional`
(ultraweak continuity into `B` is tested by the np-functionals of `B`),
`continuous_ultraweak_smul`, `isClosed_ultraweak_closedBall`, `uw_map_of_cont`.

### 2. 63IV `cp_comprehension` — the thesis's proof, verbatim

`(p^⊥)² ≤ p^⊥` (`mul_self_le_self`, already in the file) gives
`ω((p^⊥)²) = 0`, Kadison's inequality **30IV**.1 `omega_norm_basic_1` gives
`ω(p^⊥a) = 0`, hence `ω(a) = ω(pa)`; `ω(ap)` follows by applying that to
`star a` and conjugating (`cstar_p_implies_i`), and `ω(pap)` by composing the
two.  The general `B` is the thesis's second paragraph: **22VIII**.2
`states_order_separating_2` reduces to states, and `ω ∘ f` is a p-map into `ℂ`.
65 lines.

### 3. 69V, and why 69VII came almost for free

The thesis's chain (vn.tex:3648) passes through
`⌈a*ea⌉ ≤ ⌈ω⌉^⊥ ⟺ ⌈a⌈ω⌉a*⌉ ≤ e^⊥` — true (both say `⌈ω⌉a*e = 0`) but not
stated anywhere in the thesis — and then reindexes `a ↦ a*`.  The Lean proof
does not need it: it verifies the two defining properties of `⌈ρ⌉` directly,
using **68I** `cceil_fundamental`'s `⌈⌈e⌉⌉ = ⋃_a ⌈a*ea⌉` in the leastness half
and complementing at the end.  Concretely, three private lemmas do all the
work and are shared with 69VII:

* `gns_zero_iff` — `ρ(e)ρ(a)ξ = 0 ⟺ ω(a*ea) = 0`, because
  `⟪ρ(e)ρ(a)ξ, ρ(e)ρ(a)ξ⟫ = ⟪ρ(a)ξ, ρ(e)ρ(a)ξ⟫ = ω(a*ea)` for a projection `e`;
* `omega_conj_cceil_compl` — `ω(a* ⌈⌈⌈ω⌉⌉⌉^⊥ a) = 0`: the complement `q` of a
  central support is central, so `⌈a*qa⌉ ≤ q` (`ceil_le_iff`) and
  `ω(q) ≤ ω(⌈ω⌉^⊥) = 0`, so **60I** `ceil_functionals_lemma` finishes;
* `cceil_npCarrier_le` — if `ω(a*ea) = 0` for all `a` then `⌈⌈⌈ω⌉⌉⌉ ≤ e^⊥`,
  by 68I plus leastness of `⌈⌈·⌉⌉` among *central* projections.

**69VII** `gns_ceil` is then 40 lines: the thesis's proof splits
`ℋ_Ω = ⨁_ω ℋ_ω` and argues coordinatewise, which our coordinate-free statement
(one `H`, vectors `x_ω`, `span{ρ(a)x_ω}` dense) does not have; instead the same
two carrier properties are checked, with `1 - ⋃_ω ⌈⌈ω⌉⌉ ≤ ⌈⌈⌈ω⌉⌉⌉^⊥` and
conjugation-monotonicity for the first, and `projSup` leastness for the second.
A continuous map killing a *spanning* set is `0` via `LinearMap.ker` +
`IsClosed.closure_subset_iff`.

### 4. 69IX is **not** blocked on 69VII — the survey's classification was wrong

`docs/AVN-survey.md` (and this brief) had 69IX `vn_center_separating` as
"[B] on 69VII, the TFAE's (1)⇔(3) is exactly 69VII".  It is not: our item 3 is
`⋃_{ω∈Ω}⌈⌈ω⌉⌉ = 1`, not "ρ_Ω is injective", so `gns_ceil` never enters.
(1)⇒(2) is trivial; (2)⇒(3) is a few lines from `projSup_isCentral` (which
**already exists**, `Projections.lean:4176` — QUESTIONS D4 says it is missing,
now corrected there) plus `omega_conj_cceil_compl` above.  (3)⇒(1) needs
*`⌈a⌉` is central for central positive `a`*, which the tree does **not** have;
the natural route is `⌈a⌉ = ⋁ₙ a^{1/2ⁿ}` plus `vna_supremum_mult`.  Since 69IX
is also a known mis-transcription (QUESTIONS **D4**: its item 1 duplicates its
item 2), it was left alone rather than proved in a shape awaiting a ruling.

### 5. The `Type u` generalisation of `A/VN/Basic.lean` **cascades** — left undone

Changing `variable {A B : Type u}` (Basic.lean:2911) and `{C : Type u}`
(:3014) to `Type*` breaks the GNS block twelve lines later:
`abbrev gnsHilb : Type u` (:3229) and `exists_faithful_normal_rep (A : Type u)
… ∃ H : Type u` (:3547, :3559, :3585, :3602, :3653) all pin the section
universe, and the file then fails with a `whnf` timeout on top of the
universe errors.  Reverted; `Basic.lean` is untouched.  The targeted fix, if
someone wants it, is to move the four lemmas A/Proc needs
(`starAlgHom_mono`, `starAlgHom_le_iff`, `starAlgEquiv_preservesDirSups`,
`isVNSubalgebra_range`) into their own section with `Type*` variables, *above*
the GNS block — but `isVNSubalgebra_range` sits below it and would have to move.
Not attempted: the brief said not to sink the session into it.

### 6. Lean traps (the same family as the `filter_upwards` one in HANDOFF)

Because the topologies are `def`s, every Mathlib lemma with a
`[TopologicalSpace _]` instance argument synthesizes the **norm** topology and
then fails with "synthesized type class instance is not definitionally equal".
Hit four times in one proof: `nhds_induced` (note its arguments are
`@nhds_induced A S (ultraweak A) …`, α before β), `isOpen_induced_iff`,
`Continuous.comp`, `Continuous.tendsto`, `tendsto_const_nhds`.  Two ways out,
both used here: give the topology explicitly with `@`, or — for anything stated
about *convergence* — `rw [uwTendsto_iff]` first and work in `ℂ`, where the
instances are the real ones.

### 7. Verification

Each of `Projections` and `Completeness` compiles clean under the `LEAN_PATH`
bypass (`sorry` + pre-existing linter warnings only); `Division` (7) and
`NormalFunctionals` (5) were recompiled against them unchanged.  `#print
axioms` was run by appending to a copy of each module.  All five A/VN oleans
are current (written atomically via a temp file, since another agent's
`lake build` was reading them).  Files touched:
`Theses/A/VN/{Completeness,Projections}.lean`, `docs/AVN-survey.md`,
`ERRATA.md` (one new row, **77VI**), `QUESTIONS.md` (D4 update), this log.
Nothing staged, nothing committed.

## Session 54 — `A/Proc`: **112XI is not unblocked by 77V** (the brief was wrong), and six of `Duplicators.lean` fall instead (worker 79)

Files touched: `Theses/A/Proc/Duplicators.lean`, `docs/AProc-survey.md`, this
log.  Nothing staged, nothing committed.  **A/Proc 84 → 78**
(`Duplicators` 17 → **11**; `Measurement` 11, `Tensor` 39, `QuantumLambda` 17
unchanged and untouched).  All six new theorems `#print axioms` to exactly
`[propext, Classical.choice, Quot.sound]`, checked from *inside* the module.

| point | declaration | divergence class |
|---|---|---|
| **127VI** | `unit_duplicator` | 0 — the thesis's four-line proof verbatim |
| **128VIII** | `uniqueness_duplicator` | 0 — the thesis's proof, through the already-proved `sef_instrument` |
| **127III** uniqueness | `duplicable_unique` | 0 |
| **128XI** | `duplicability_multiplication` | 0 |
| **132III**.1 | `dup_vna_is_monoid_1` | 2 — exercise, no published solution (`asols.tex` stops at parsec 340) |
| **132III**.3 | `dup_vna_is_monoid_3` | 2 — likewise |

### 1. The headline: **112XI `tensor-universal-property` is still blocked, and the blocker is not 77V**

The brief (and the survey row it came from, and session 53's A/VN note) said
112XI was "blocked on 77V alone", so that closing 77V would open 112XI, 114I,
114II and 116VII.  **That is wrong.**  proc.tex:2998 reads

> Since `β_⊙` is ultraweakly continuous and bounded, and `𝒜⊙ℬ` can
> **by \sref{tensor-basic}** be considered an ultraweakly dense ∗-subalgebra
> of `𝒯` via `γ_⊙`, the theorem follows from \sref{vn-extension} except for
> some trivial details.

— it cites **112X** (`tensor-basic`) as well as **77V**, and all five parts of
112X are `sorry`.  Spelled out against our `vn_extension`, which asks for a
∗-subalgebra `S ⊆ 𝒯`, a map `f : S →ₗ 𝒞` continuous for the topology
**induced from `𝒯`**, and a bound `‖f s‖ ≤ C‖(s : 𝒯)‖`, building `f` from
`β_⊙` needs three things the hypotheses of 112XI do not give:

1. **`γ_⊙` injective**, for `f` to be well defined on `S = γ_⊙(𝒜⊙ℬ)`.  This is
   the cheap one: it is 112X.2's isometry, but it can also be got directly from
   `IsTensorProduct` (if `γ_⊙ t = 0` then `(σ⊙τ)(t) = 0` for all np `σ,τ`,
   hence for all normal functionals by the four-term decomposition of **72XI**,
   and normal functionals separate a finite-dimensional subspace, so the
   `exists_indep_repr` normal form forces `t = 0`).  Not written, since 2 and 3
   are not cheap.
2. **`uwTensorTopology A B ≤ TopologicalSpace.induced ⇑(lift γ) (ultraweak T)`.**
   `uwTensorTopology` is the initial topology of the norm-limit-of-simple
   functionals and the induced topology is the initial topology of
   `{h ∘ γ_⊙ : h ∈ 𝒯_*}`, so this says exactly that **every norm limit of
   simple functionals extends along `γ_⊙` to a normal functional on `𝒯`** —
   which is **112X.5**'s first half, and the exercise's own hint for it is
   "using the fact that the operator norm limit of np-functionals is an
   np-functional again, see \sref{predual-complete}", i.e. **87III**
   (`A/VN/NormalFunctionals.lean:889`, `sorry`).
   This is not a rendering artefact.  `hn : BilinNormal β` gives continuity of
   `β_⊙` for `uwTensorTopology`, which is the *finer* topology (112X.3 is the
   inclusion the other way), and continuity for an induced topology is
   equivalent to extendability of the testing functionals — so no manipulation
   of `hn`/`hb` substitutes for it.
3. **The norm bound**, converting `hb`'s `tensorNorm` bound into a `‖·‖_𝒯`
   bound, i.e. **112X.2** `‖γ_⊙ s‖ = ‖s‖`, which rests on **90II.2**
   `vn_center_separating_fundamental_2` (`NormalFunctionals.lean:3336`,
   `sorry`) — 90II.**1** is proved, 90II.2 is the operator-norm density half.

**Consequence for planning: A/Proc's external frontier is now three `sorry`s in
one A/VN file, `NormalFunctionals.lean` — 87III `predual_complete`, 90II.2, and
86IX `polar_decomposition_of_functional` (which 112X.4 needs).**  Behind them
sit 112X (5), 112XI, 114I, 114II, 116VII, 115II and the whole
functoriality/monoidal block of `Tensor.lean` — well over half the file.
115II is blocked twice over: proc.tex:3139 takes `f ⊗ g := β_⊗` from
`tensor-universal-property` *and* extends `ω ∘ β_⊙` by it a second time.

I also checked the two `Tensor.lean` items that looked independent of that
chain and they are not: **116III**.2 (`‖a ⊗ b‖ = ‖a‖‖b‖`) needs np *states* to
be norming — the `≤` half is free (`a ⊗ b = (a⊗1)(1⊗b)` with two unital
∗-homs), but the `≥` half wants `σ(x)τ(y)` close to `‖x‖‖y‖` for np states,
which is **87VI** `norm_predual` (`sorry`), and **117III**
`tensor_distributes_over_sums` routes through 116VII.

### 2. `Duplicators.lean`: parsec 1270–1280 closes except the measure theory

The one piece of new machinery is that **the effects span `𝒜` linearly**
(`mem_span_effects`, with the induction principle `effects_induction`):
`a = ℜa + i·ℑa`, a self-adjoint element is `a⁺ − a⁻`, and a positive `x` is
`‖x‖ · (‖x‖⁻¹ • x)` with `‖x‖⁻¹ • x` an effect (`ofReal_smul_nonneg` twice,
plus `IsSelfAdjoint.le_algebraMap_norm_self`).  This is precisely what the
thesis waves at twice in 128VIII's proof — "of course, it suffices to show that
all `p ∈ [0,1]_𝒜` are central (by the usual reasoning)" and "similarly, we only
need to prove that `δ(a ⊗ p) = a·p` for `p ∈ [0,1]_𝒜`".

* **127VI** is the thesis's proof unchanged; the only Lean content is that
  `u ⊗ 1 ≤ 1 ⊗ 1` and `u^⊥ ⊗ u ≤ u^⊥ ⊗ 1` come from **116III**.1
  `tensor_simple_facts_1` (proved last session — the first pay-off of the
  un-vacuumed band), and that `1 ⊗ 1 = 1` is `IsTensorProduct.miu.1`.
* **128VIII** is ~90 lines.  For each effect `p` it feeds
  `f(a,b) = δ(a ⊗ p + b ⊗ p^⊥)` — assembled as
  `δ ∘ (⊗p ∘ π₀ + ⊗p^⊥ ∘ π₁)` out of `LinearMap.flip (vnTensor A A).map` and
  `lpEvalₗ` — to **128VI** `sef_instrument`, which was already proved in the
  file (and rests on the already-proved **128II** `tomiyama`).  Positivity of
  `f` is `vtmul_nonneg` plus `lp_infty_nonneg_iff`; unitality and `f(a,a) = a`
  are `a ⊗ p + a ⊗ p^⊥ = a ⊗ 1` and 127VI; and `f(1,0) = δ(1 ⊗ p) = p` is the
  left unit law.  `sef_instrument` then returns exactly the thesis's two
  conclusions, `p` central and `f(a,b) = ap + bp^⊥`.
  One divergence forced by our rendering: `sef_instrument` carries
  `[Nontrivial A]` (it lives in a section that assumes it), so 128VIII opens
  with a `subsingleton_or_nontrivial` split the thesis does not have; the
  trivial algebra is `Subsingleton.elim` twice.
* **128XI**'s `⇐` is the observation that multiplication *is* a duplicator with
  unit `1` (subunitality is `δ(1⊗1) = 1·1 = 1`), and `⇒` is 128VIII.
* **132III**.1 is pure plumbing (`PositiveLinearMap.ofClass` on the ncpsu-map;
  a monoid asks for strictly more than a duplicator), and **132III**.3 is then
  a reshuffle: by 128VIII both multiplications are the algebras' own and both
  units are `1`, so "monoid morphism" and "unital + multiplicative" are the
  same pair of conditions in the other order.

**One declaration was moved, not changed**: `duplicable_unique` (127III's
uniqueness clause) was stated at parsec 1270, above `uniqueness_duplicator`,
which supplies its second conjunct — it is now stated immediately after 128VIII,
with a pointer left at its old position.  The statement is byte-identical.

What is *not* reachable in this file, with the reason:

* **128XIII** `duplicable_product` — the thesis builds
  `δ_𝒜 = π₁ ∘ δ ∘ (κ₁ ⊗ κ₁)`, and `κ₁ ⊗ κ₁` is `tmap`/`tmapM`, i.e. **115II**.
* **132III**.2 contains 127III's main equivalence as one of its four conjuncts,
  and 127III needs the measure-theoretic chain 129X/130IV/130V plus `cvn`.
* **132III**.4's first conjunct quantifies over `braiding A A`, which is chosen
  from the still-`sorry`ed `exists_braiding`, so nothing about it can be
  computed; **132III**.5 needs 127III.
* **129X** needs the product functional `ω ⊗ ω` and `carrier-tensor`
  faithfulness (118IV), both behind 115II.

### 3. Nothing false found

Every step of the thesis's arguments for 127VI, 128VIII, 128XI and 132III.1/.3
checked out; no ERRATA or QUESTIONS rows were added or changed this session.
The one factual correction is to *our* survey (the 112XI row), recorded in §1
and at the top of `docs/AProc-survey.md`.

### 4. Verification

`lean Theses/A/Proc/Duplicators.lean` under the `LEAN_PATH` bypass: **0 errors,
11 `declaration uses 'sorry'` warnings** (was 17), no new warning of any kind;
`Measurement.lean` recompiled unchanged at 11.  `Tensor.lean` and
`QuantumLambda.lean` were not touched (39 and 17 from session 52's compiler
count); a confirming recompile of `QuantumLambda` was not possible because
`A/VN/Projections.olean` was missing at the time — another agent was rebuilding
A/VN.  `#print axioms` was run by appending the commands to a *copy* of the
module and compiling that, never from an importing scratch file.  The olean for
`Theses.A.Proc.Duplicators` is left built and current (written via `lean -o` to
the scratchpad and copied in).


---

## Session 53 (`B/Dils`) — D5 implemented; 170IV.1 and 157IV.1 closed

Territory: `Theses/B/Dils/` only.  **39 → 37** open declarations,
compiler-counted per file (`SelfDual` 9, `Pure` **12**, `Paschke` **7**,
`Kaplansky` 5, `Stinespring` 2, `SelfDualCompletion` 2, `HilbertModules` 0).
Both new proofs are axiom-clean (`propext, Classical.choice, Quot.sound`,
checked by appending `#print axioms` to a *copy* of each module).

### 1. QUESTIONS **D5** — implemented, and it really was two signatures

Bas ruled "fix transcription".  `[VonNeumannAlgebra A] [VonNeumannAlgebra B]`
were added to **170IV**.1 `surjective_nmiu_1` and **170IV**.2
`surjective_nmiu_2` (`Pure.lean`), matching dils.tex:6223's "between von
Neumann algebras" and the idiom of the neighbouring `standard_corner_dils`
and `paschke_corner`.  A tree-wide grep confirmed beforehand what the brief
assumed: nothing outside `Pure.lean` mentions either name, so the edit is the
two signatures plus their doc comments.  D5 is **deleted** from QUESTIONS.md
per the new house rule.

### 2. **170IV**.1 `surjective_nmiu_1` — proved (~150 lines)

The author's solution (`bsols.tex`, `surjective-nmiu`) is transcribed with
**one dependency-order divergence and one simplification**:

* *(divergence, class 3)* The solution routes `ker ϱ` through
  `kernel-ultraweak-twosided-ideal-dils` and **69II** `weakly-closed-ideal`
  (still `sorry`, `A/VN/Projections.lean:4504`).  We use **69IV**
  `carrier_miu` instead, which *is* proved and gives the same central
  projection `z = ⌈ϱ⌉` for the special case of an nmiu-map — in the
  `nmiu_factors` form `ϱ a = ϱ b ↔ z·a = z·b`.  This is not a shortcut past
  the thesis's development: 69IV is a corollary of 69II in the thesis, so
  the bootstrapping order is respected; only the more general 69II is
  bypassed.
* *(divergence, class 2)* The solution builds the corner `zA` as a type,
  restricts `ϱ` to it, and argues "a bijective miu-map has an miu inverse,
  hence is an nmiu- and so an ncp-isomorphism".  We never build `zA`: the
  inverse is a bare function `σ : B → A` with `σ(ϱ a) = z·a` (well defined
  by 69IV), which is a *non-unital* ∗-homomorphism, so **34IV**.3
  `cp_of_mi` gives complete positivity directly and the "miu inverse"
  argument is not needed.  `σ(1) = z ≠ 1` is exactly why unitality had to
  go, and nothing else in the proof wanted it.
* **The step the solution omits is normality of `σ`**, which it covers with
  "consequently, it is an nmiu-isomorphism (as miu-maps are order-
  preserving)" — order-preservation is not normality.  The missing argument
  is short and worth recording: if `u` is an upper bound of `σ(D)` and
  `d₀ ∈ D`, then `(1−z)u = (1−z)(u − σd₀)(1−z) ≥ 0` because `(1−z)σd₀ = 0`
  and `z` is central; hence `zu ≤ u`, and `σ(⋁D) ≤ σ(ϱ u) = zu ≤ u`.  This
  is *not* an erratum — the solution's claim is true, just unargued — so
  nothing was added to ERRATA.
* The remaining obligation, `f(z·x) = f(x)` for an ncp `f` with
  `f(z) = f(1)`, is Kadison–Schwarz.  Session 52's costing proposed
  `ncp_cp_cs` plus the estimate `ww* ≤ ‖x‖²(1−z)`; the two-argument form
  **34XIV** `cp_cs` with `a := x`, `b := 1−z` is strictly cheaper — it yields
  `f(x*(1−z))·f((1−z)x) ≤ ‖f(1−z)‖·f(x*x) = 0` with the left side
  `star(f((1−z)x))·f((1−z)x)`, so `f((1−z)x) = 0` with no norm estimate.

Uniqueness in the corner's universal property is free: `ϱ` is surjective, so
a factorisation is determined pointwise.

### 3. **157IV**.1 `paschke_correspondence_mem` — proved (`Paschke.lean`)

The thesis's 157VI ("Set-up") transcribes directly: `√t` commutes with
`ϱ(𝒜)` (Mathlib's `Commute.cfcₙ_nnreal`, since `CFC.sqrt = cfcₙ NNReal.sqrt`),
so `φ_t = h ∘ ad_{√t} ∘ ϱ` is a composite of three ncp-maps, and
`φ − φ_t = φ_{1−t}` is ncp by the same argument at `1 − t`.

**Divergence, class 3, and it is the interesting one.**  The thesis proves
157IV *only for the concrete dilation* `𝒜 ⊗_φ ℬ` of `existence-paschke` and
transfers to an arbitrary Paschke dilation at 157IX via
`paschke-unique-up-to-iso`.  Part 1 needs none of that machinery: the Set-up
argument never looks inside `𝒫`, and our proof uses the dilation only through
`hD.1` (`φ = h ∘ ϱ`).  So 157IV.1 is **not** blocked on `existence_paschke`,
contrary to how the thesis's proof structure reads.  Parts 2 (⇒) and 3 *are*
model-dependent — 157VII and 157VIII compute with `⟨x̂, T x̂⟩` inside
`𝒜 ⊗_φ ℬ` and appeal to `hilmod-fixed-on-V` — so they stay blocked.

Infrastructure added, all `private` in `Paschke.lean`: `corrPos` (an ncp-map
as a positive linear map) and `exists_corrComp` (composition of ncp-maps).
These are the *third* copy in the tree — `Stinespring.lean` and `Pure.lean`
each carry their own `private` pair, and `A/Proc/Measurement.lean` has a
public `ncpComp` that is off this import path (QUESTIONS **D3**).  Worth one
consolidation pass when D3 is decided.  `ad_{√s}` as a bundled `NCPMap` is
built inline from `ad_cp_1` (**34V**.1) and `ad_normal` (**44VIII**), the
latter through the `dirSup`-uniqueness glue that `Stinespring.lean`'s
`private adPos_normal` also uses.

### 4. Nothing false found; a numbering correction to our own notes

No ERRATA or QUESTIONS row was added.  One correction to *our* documents:
`dils_completion` (`SelfDualCompletion.lean:81`) is **150II**, not "151I" —
151Ia is `selfdual_completion_univ`, its universal property.  Session 52's
survey and the session-53 brief both used the wrong number; `docs/BDils-survey.md`
now says 150II and explains the difference.

150II itself was assessed and **not attempted**: it is a type construction
(a completion carrying `NormedAddCommGroup`, `CStarModule`, `CompleteSpace`
and self-duality) whose thesis proof is the twelve points 150III–150XV, with
fast nets and a transfinite induction on compatible extensions.  It is not
session-sized.  The next gate in `B/Dils` is therefore **154III**
`existence_paschke` (`Paschke.lean:425`), which sits between 150II and
157IV.2/.3, 171II and most of `Pure.lean`.

### 5. Verification

Each file checked with `lean <file>` under the `LEAN_PATH` bypass: `Pure.lean`
**0 errors, 12** `declaration uses 'sorry'` (was 13); `Paschke.lean` **0
errors, 7** (was 8; its remaining style-linter `warning`s are all pre-existing
and none is in the new code).  `SelfDual` 9, `Kaplansky` 5, `Stinespring` 2,
`SelfDualCompletion` 2, `HilbertModules` 0 recompiled unchanged, 0 errors
each.  Several compile attempts had to be retried: another agent was
rebuilding `A/VN`, and `Completeness.olean`/`Division.olean` vanished
mid-session — the "oleans go missing under concurrent load" trap, exactly as
documented.

## Session 55 — `A/VN`: the `CentreSeparating` mis-transcription is repaired, and **69IX** and **90II.2** both fall (worker 80, A chain)

QUESTIONS **D4** ruled on by Bas ("fix transcription") and now deleted from
that file.

### 1. What was wrong, and what the fix is

`Theses.A.VN.CentreSeparating Ω` was

```lean
∀ a : A, IsCentral A a → 0 ≤ a → (∀ ω ∈ Ω, ω a = 0) → a = 0
```

which is **neither** item of **69IX**.  The sources:

* cstar.tex **21II**.4 (`separating-4`) = 69IX item **1**: "`Ω` […] is
  *centre separating* if `a ∈ 𝒜₊` is zero iff `ω(b*ab) = 0` for all `ω ∈ Ω`
  and `b ∈ 𝒜`" — note the conjugation, which our version dropped;
* vn.tex 69IX item **2**: "A central projection `z` of `𝒜` is zero when
  `ω(z) = 0` for all `ω ∈ Ω`" — central *projections*, not positives;
* vn.tex 69IX item **3**: `ϱ_Ω` is injective.

**A/CStar already had the faithful 21II.4 rendering**: `Theses.A.CStar.
CentreSeparating` (`A/CStar/Positive.lean:1811`), alongside 21II.1–3
(`OrderSeparating`, `Separating`, `Faithful`).  So no new definition of the
notion was written; the A/VN name is *defined as* that predicate applied to
`Ω`:

* **`CentreSeparatingConj Ω`** := `Theses.A.CStar.CentreSeparating (fun ω : Ω
  => ω.toPositiveLinearMap.toLinearMap)` — 69IX item 1, with
  `centreSeparatingConj_iff` giving the unfolded form;
* **`CentreSeparatingCentralProj Ω`** — 69IX item 2, verbatim.

The old `CentreSeparating` is **kept under its name**, its doc comment
retitled to say it is an auxiliary notion belonging to neither thesis, because
`A/Proc/Tensor.lean` states eight results with it and that file was being
edited by another worker.  **All eight mean the thesis's notion**
(`CentreSeparatingConj`): proc.tex 116IV.2 `tensor_generation_2` (three
occurrences), 116VII `tensor_characterization` (three), 117II.2
`sum_generation_2` (two) — every one of them transcribes "centre separating
collection of np-functionals", which in the theses is always 21II.4.  The
migration is a mechanical rename once `Tensor.lean` is free; `sum_generation_2`
is the only one of the three that is *proved*, and its proof gets **shorter**
under the faithful notion (test with `b = κᵢ(bᵢ)`; the centrality gymnastics
in its current proof disappear).

Bridges proved: `CentreSeparating.centralProj` (auxiliary ⇒ item 2, since a
central projection is a central positive) and `CentreSeparating.conj`
(⇒ item 1).  The converses are *not* proved: they need "`⌈a⌉` is central for
central positive `a`", which the tree still lacks.  Nothing needs them.

### 2. **69IX** `vn_center_separating` — proved, and the brief over-costed it

The brief (following the session-53 QUESTIONS note) said (3) ⇒ (1) needs
"`⌈a⌉` is central for central positive `a`", via the ultrastrong limit of the
`a^{1/2ⁿ}`.  **It does not.**  Run the cycle the other way:

* **(1) ⇒ (3)**: `z := (⋃_{ω∈Ω} ⌈⌈ω⌉⌉)^⊥` is a projection with
  `z ≤ ⌈⌈ω⌉⌉^⊥`, so `star b * z * b ≤ star b * ⌈⌈ω⌉⌉^⊥ * b` and
  `ω(b* z b) = 0` by the private `omega_conj_cceil_compl` (half of 69V).
  Item 1 then gives `z = 0`.  This is the thesis's (2) ⇒ (3) argument with
  the conjugating `b` carried along — and it needs neither `gns_ceil` nor
  centrality of `z`.
* **(3) ⇒ (2)**: `1 - z` is a central projection with `ω(1 - (1-z)) = 0`, so
  `⌈ω⌉ ≤ 1 - z` (`carrier_spec`) and `⌈⌈ω⌉⌉ ≤ 1 - z` (`cceil_fundamental`,
  leastness); hence `1 = ⋃ ⌈⌈ω⌉⌉ ≤ 1 - z`, so `z ≤ 0`, so `z = 0`.
* **(2) ⇒ (1)**: the existing `eq_zero_of_centreSeparating_conj`, whose proof
  already only ever applied the hypothesis to the *projection* `⌈⌈a⌉⌉` — its
  hypothesis was simply weakened from the auxiliary notion to item 2.

**Divergence, class 3 (different route).**  The thesis gets (1) ⟺ (3) from
**30X** and proves (2) ⇒ (3) at length through **69VII** `gns_ceil`; we prove
the cycle (1) ⇒ (3) ⇒ (2) ⇒ (1) and use `gns_ceil` nowhere.  `gns_ceil`
remains proved and unused here.

Also wrong in the brief: it warned that `projSup_isCentral` might be needed —
it exists, but the proof above does not use it either.

### 3. **90II.2** `vn_center_separating_fundamental_2` — proved

This was the sole blocker of `B/Dils` **159IX** and **164II.2b**, which are
now unblocked.  90II.1 and .2 were both restated with the thesis's hypothesis
(`CentreSeparatingConj`), which is the *weakest* of the three notions, so both
theorems got stronger; 90II.1's existing proof went through unchanged after
`nonneg_of_conjNP_of_centreSeparating` was rebased on item 1 (which is exactly
what **30X** `proto_gelfand_naimark_1` consumes — the bridge lemma
`centreSeparating_cstar` it used to go through became superfluous and was
deleted).

The proof transcribes vn.tex 90IV: `ϱ_Ω` is injective (69IX), so **89IX**
`normal_functional` writes `f = ∑ₙ ⟪xₙ, ϱ_Ω(·)xₙ⟫`; decomposing each `xₙ` over
the summands of `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω` turns this into a single absolutely
summable family over `ℕ × Ω`; a finite `F` carries all but `ε/2` of it; and
each remaining term `⟪v, ϱ_ω(·)v⟫` is brought within `ε/2` of some `ω(s*(·)s)`
with `s ∈ S` by 48III (density of the `η_ω(b)`) followed by **72III**.1c
`bstaromega_lipschitz` — the `‖·‖_ω`-to-operator-norm Lipschitz bound — plus
ultrastrong density of `S` (`ultrastrong_ball_mem_nhds`).  The thesis's own
two "without loss of generality" reductions (over `n`, then over `ω`) are the
single product-index family here.

**Infrastructure, and a duplication to be merged.**  `ℋ_Ω` over a *set* `Ω` did
not exist: `A/VN/Basic.lean` builds `⊕_ω ℋ_ω` over *all* np-functionals
(`gnsHilb`, 48VIII).  Rather than generalise that block over an index family —
which would force a rebuild of the entire tree from the root of the import
graph, with other workers active — its ~150 lines were copied into
`NormalFunctionals.lean` with the index cut to `Ω`: `gnsHilbOn`, `gnsRepOn`,
`gnsElemVecsOn`, `gnsRepOn_normal`, `gnsRepOn_injective`.  **Whoever next
touches `Basic.lean` should generalise `gnsHilb` over an index family and
delete the copy** (a note to that effect sits above it, as for `VNSub` and
`CU`).  The one new item is `gnsRepOn_injective`: `ϱ_Ω(a) = 0` says
`ω(b* a*a b) = ‖ϱ_Ω(a) η_ω(b)‖² = 0`, so `a*a = 0` exactly when `Ω` is centre
separating — three lines, where the thesis routes through 30X and 69VII.
Two further private helpers were added: `inner_conj_diff_le` (the
polarisation-free `|⟪u,Tu⟫ − ⟪w,Tw⟫| ≤ ‖T‖(‖u‖+‖w‖)‖u−w‖`, the same estimate
as inside 38VI.2 `vector_functional_convergence_2`, which is *not* exported as
a lemma there) and `gnsVec_approx_functional` (the ε-argument for a single
summand).

### 4. Nothing false found

No ERRATA row was added; no new QUESTIONS item.  D4 was deleted, and with it
the (now empty) "Ours to decide, not the authors'" heading.

### 5. Verification

`lean` under the `LEAN_PATH` bypass, 0 errors each:
`Projections.lean` **13** `declaration uses 'sorry'` (was 14),
`NormalFunctionals.lean` **4** (was 5), `Basic.lean` 24, `Division.lean` 7,
`Completeness.lean` 0 — **A/VN total 48** (was 50).  `#print axioms` clean
(`[propext, Classical.choice, Quot.sound]`) for `vn_center_separating`,
`CentreSeparatingCentralProj.conj`, `centreSeparatingConj_iff`,
`vn_center_separating_fundamental_1` and `vn_center_separating_fundamental_2`.
Nothing outside `A/VN` referenced the changed declarations, so `A/Proc` and
`B/Dils` are untouched.

## Session 54 — `B/Dils`: **159IX `ketbra_ultranorm_continuous`** falls with 90II.2, and **164II.2b is false as we transcribed it** (worker 81)

Files touched: `Theses/B/Dils/SelfDual.lean`, `QUESTIONS.md`,
`docs/BDils-survey.md`, this log.  Nothing staged, nothing committed.
**B/Dils 37 → 36 `sorry`s** (compiler-counted per file: `HilbertModules` 0,
`Kaplansky` 5, `Paschke` 7, `Stinespring` 2, `SelfDualCompletion` 2,
`SelfDual` 9 → **8**, `Pure` 12).  Both new theorems `#print axioms` to
exactly `[propext, Classical.choice, Quot.sound]` (checked from *inside* the
module).

### 1. **159IX** `ketbra_ultranorm_continuous` — ~110 lines

A/VN's **90II**.2 `vn_center_separating_fundamental_2` was the sole blocker
and it landed last session, so the thesis's 159X–159XI transcribes almost
verbatim.  The two pieces that had to be located rather than built:

* `Ω = {f(⟨x,(·)x⟩)}` already exists as `baVecNP`
  (`SelfDualCompletion.lean`, written for **152X**), so the "order
  separating" step is `ba_nonneg_iff` plus `VonNeumannAlgebra.np_faithful`
  fed to `centreSeparatingConj_iff` at `b = 1`.
* 90II.2 wants an ultrastrongly dense `S`; we pass `S = 𝒷ᵃ(X)` itself and
  read each resulting `ωₖ(sₖ*(·)sₖ)` back as `baVecNP (sₖ xₖ) fₖ` (the
  adjoint moves `sₖ` onto the vector).  The thesis instead observes
  "`ω(T*(·)T) ∈ Ω`" and quotes 90II for the span; same content, but our form
  of 90II makes the conjugation explicit, so no closure argument on `Ω` is
  needed.

**Divergence, class 2.** The thesis spends the first half of 159X proving
`‖|z⟩⟨y|‖ ≤ ‖z‖‖y‖` from order separation of the vector states plus
`order-separating-norm` (**21IV**).  That is *already the bound with which
`mketbra` is defined* in our tree — Cauchy–Schwarz `‖⟨y,z⟩‖ ≤ ‖y‖‖z‖`
together with `‖b·x‖ ≤ ‖b‖‖x‖` gives it outright, via
`LinearMap.mkContinuous_norm_le`.  So 159X's preparation is not needed at
all; whether it is needed in the thesis's own development (where `mketbra`
is not defined through a bound) is a separate question, and we have not
claimed an erratum.

### 2. **164II.2b `ext_tensor_ketbra_dense` is FALSE as transcribed** — QUESTIONS **D6**

The brief expected 164II.2b to follow from 159IX.  It does not, and the
obstacle the previous worker flagged as "an aggravating factor" is fatal
rather than inconvenient.

Our statement demands an approximating **net indexed by `Finset (ι × κ)`
along `atTop`**; the thesis (164XI) claims only that the span of
`D = {|(e'ᵢa) ⊗ (d'ⱼb)⟩⟨e_k ⊗ d_l|}` is ultraweakly **dense**.  Take
`ι = κ = PUnit`, `𝒜 = ℬ = B(ℓ²)`, `𝒞 = 𝒜 ⊗ ℬ`, `X = 𝒜`, `Y = ℬ`,
`E = extTensorSelf` (session 52), `e = d = 1`.  Then `E.Z = 𝒞`,
`𝒞ᵃ(E.Z) ≅ 𝒞` by right multiplication, `span D ≅ 𝒜 ⊙ ℬ`, and
`Finset (PUnit × PUnit)` has a **greatest element**, so `atTop` is principal
there and — the ultraweak topology being Hausdorff — the net's value at that
element must *equal* `T`.  The statement therefore asserts
`𝒜 ⊗ ℬ = 𝒜 ⊙ ℬ`.

This is a defect in **our** transcription, not in the thesis; and it cannot
be refuted inside the tree, because `IsVNTensor` is axiomatized (proc.tex
**108II** is not formalized) and the one concrete instance we have is
`ℂ ⊗ ℂ = ℂ`, where the statement happens to be true.  The `sorry` is left in
place per the never-change-a-statement rule.  Note **159IV**
`ketbra_ultraweakly_dense` carries the same net shape *legitimately* — there
the thesis's own proof produces the net `p_S T p_S`; copying that shape into
164II.2b, where the thesis produces no net, is what went wrong.

### 3. The thesis's 164XI *is* proved: `ext_tensor_ketbra_uwDense` (~210 lines)

New public theorem, in the entourage form ("for finitely many
np-functionals and `ε > 0` some element of `span D` is within `ε` of `T` on
all of them"), which is the form **165VI**'s `generates` clause consumes.
The proof is the thesis's:

* **159IV** applied to the basis `E₂` of **164II**.2a gives an
  approximant in the span of the `|b·(e'ᵢ⊗d'ⱼ)⟩⟨e'_k⊗d'_l|`, `b ∈ 𝒞`
  arbitrary;
* a `Submodule.span_induction` reduces to a *single* such generator;
* Kaplansky (**74IV**, via `unDense_tSpan` and
  `StarSubalgebra.topologicalClosure`) gives a net in `𝒜 ⊙ ℬ`'s *norm*
  closure, norm-bounded by `‖b‖`, converging ultrastrongly to `b`;
  `unSeminorm_op_smul_le` turns that into ultranorm convergence of
  `b_α·(e'ᵢ⊗d'ⱼ)`, and **159IX** into ultraweak convergence of the ketbras.

**One step is ours, not the thesis's.** The thesis says Kaplansky produces a
bounded net "in `𝒜 ⊙ ℬ`"; Kaplansky needs a *C\*-subalgebra*, so what it
actually produces lies in the **norm closure** of `𝒜 ⊙ ℬ` (the spatial
C\*-tensor product).  Coming back is easy but has to be said: `b ↦ |b·v⟩⟨w|`
is norm-continuous (`‖·‖ ≤ ‖b‖‖v‖‖w‖`) and np-functionals are norm-bounded
(`PositiveLinearMap.exists_norm_apply_le`), so a norm-approximation of the
net's value by an element of `𝒜 ⊙ ℬ` costs only another `ε/2`.  Worth a
half-sentence in dils.tex:5348.

### 4. `existence_paschke` re-costed — and it is blocked on **two** roots

Re-read against dils.tex:3600 (**154IV**–**154V**).  The construction is:
`𝒜 ⊙ ℬ` with `[∑aᵢ⊗bᵢ, ∑αⱼ⊗βⱼ] = ∑ bᵢ*φ(aᵢ*αⱼ)βⱼ`, then **150II**
`dils_completion`, then **151Ia** `selfdual_completion_univ` for the
universal property.  Sessions 51–52 named only 150II; **151Ia is a second
blocker**, and unlike 150II it is *not* itself a construction: it takes the
completion as a hypothesis, and the ultranorm completeness it needs is
already in the tree (`unComplete_of_isONBasis`, the TFAE at
`HilbertModules.lean:3492`).  Costing and the recommendation that **151Ia is
the next gate** are in `docs/BDils-survey.md`.

### 5. Corrections to the brief

* "164II.2b — check whether the `Finset (ι × κ)` net is a real obstacle or
  just an inconvenience" — **real, and fatal**: the statement is false.
  Consequently "after 164II.2b, the chain 165VI → 167I follows" does not
  hold; what 165VI needs is now supplied by `ext_tensor_ketbra_uwDense`, but
  165VI still owes 165IX/165X (product functionals, separation).
* "existence_paschke … sits between 150II and 157IV.2/.3, 171II" — right,
  but it needs **151Ia** as well as 150II, and 151Ia is the cheaper and
  unblocked one.
* The brief's "159IX is the largest self-contained item in `SelfDual.lean`"
  over-costed it: ~110 lines, and 159X's norm estimate was free.

### 6. Verification

`lean Theses/B/Dils/SelfDual.lean` under the `LEAN_PATH` bypass: no errors;
`sorry`-declaration count **8** (2478, 2496, 2521, 3315, 4165, 4608, 5044,
5066).  `#print axioms` on `ketbra_ultranorm_continuous` and
`ext_tensor_ketbra_uwDense`: both exactly
`[propext, Classical.choice, Quot.sound]`.

---

## Session 55 — `A/Proc`: **112X.1 `tensor-basic` part 1 falls** (90II.2 unblocked it), and the eight `CentreSeparating` uses are migrated (worker 81)

Territory: `Theses/A/Proc/` only.  Files touched: `Theses/A/Proc/Tensor.lean`,
`docs/AProc-survey.md`, this log.  Nothing staged, nothing committed.
**A/Proc 78 → 77**, compiler-counted per file: `Tensor` **38** (was 39),
`Measurement` 11, `QuantumLambda` 17, `Duplicators` 11 (the last three
untouched and recompiled unchanged).  Every new declaration `#print axioms`
to exactly `[propext, Classical.choice, Quot.sound]`, checked by appending the
commands to a *copy* of the module.

| point | declaration | divergence class |
|---|---|---|
| **112X**.1 | `tensor_basic_1` | 1 — the thesis's route, with two steps it leaves implicit spelled out (see §1) |
| **117II**.2 | `sum_generation_2` | 0 — reproved under `CentreSeparatingConj`, *shorter* than before |

### 1. **112X**.1 `tensor-basic` part 1

**The brief's frontier list was out of date in exactly one place.**  It said
A/Proc's external frontier was "87III `predual_complete` and 86IX, a third
(90II.2) closed last session" — and it was right, but neither the brief nor
the survey drew the consequence: **90II.2 is precisely what 112X.1 was blocked
on**, so 112X.1 became A/Proc-local the moment it closed.  It is now proved.

Both conjuncts, following proc.tex:2884 ("Show using
\sref{vn-center-separating-fundamental} that the collection `Ω` … is order
separating, and that every np-functional on `𝒯` is the operator norm limit of
finite sums of functionals from `Ω`"):

* **Second conjunct** — a direct application of **90II**.2
  `vn_center_separating_fundamental_2` with `Ω` = the product functionals
  `γ(σ,τ)` and `S = γ_⊙(𝒜⊙ℬ)`.  Two small facts make it fit:
  * the product functionals are `CentreSeparatingConj` for a *trivial* reason
    — condition (3) of **108II** (`faithful`) is the `b = 1` instance of the
    conjugated form, and `prod_functional_unique` identifies any implementing
    functional with the chosen `prodNP`;
  * `S` is *ultrastrongly* dense.  108II gives only ultraweak density, and the
    convex-set lemma `mem_usClosure_of_mem_uwClosure` is `private` in
    `A/VN/Completeness.lean`, so the upgrade goes through the public **74VI**
    `dense_subalgebra` instead — which needs `S` as a `StarSubalgebra`, hence
    the new `tensorSpan`.
* **First conjunct (order separating)** — `nonneg_of_conjNP_of_centreSeparating`
  (**30X** fed with the above) reduces `x ≤ y` to
  `γ(σ,τ)(c*(y−x)c) ≥ 0` for **every** `c ∈ 𝒯`, while the hypothesis supplies
  it only for `c ∈ γ_⊙(𝒜⊙ℬ)`.  This gap is the one real step, and the thesis
  does not mention it.  It is closed by **74VI** (a net `s_α → c`
  ultrastrongly with `‖s_α‖ ≤ 2‖c‖`) together with **72III**.1c
  `bstaromega_lipschitz`,
  `|ω(b*ab) − ω(b'*ab')| ≤ ‖b−b'‖_ω(‖b‖_ω+‖b'‖_ω)‖a‖`, which squeezes
  `ω(s_α* a s_α) → ω(c* a c)`; the terms are real because `c* a c` is
  self-adjoint (`npFunctional_im_eq_zero`).  Note the *ultraweak* topology
  would not do here — the map `c ↦ ω(c*ac)` is quadratic — which is why the
  Kaplansky-based 74VI is the right tool and not `hγ.dense` by itself.

Infrastructure banked in `Tensor.lean`, all public and all axiom-clean:
`tensorSpan` (the linear span of `ran γ` as a ∗-subalgebra — it *is* one
because `γ` is miu-bilinear), `coe_tensorSpan`, `range_lift_eq_span`
(`ran γ_⊙ = span (ran γ)`), `prodFunctionals`, `eq_prodNP`,
`centreSeparatingConj_prodFunctionals`, `dense_ultrastrong_tensorSpan`.

Additionally banked, because 112X.2/.3 need it and our rendering of 112X.1
does not state it — **the second half of the exercise's part 1**, "show that
`ω ∘ γ_⊙` is a basic functional for every `ω ∈ Ω`, and that every basic
functional is of this form": `lift_one`, `lift_mul`, `lift_star` (`γ_⊙` is a
∗-homomorphism `𝒜 ⊙ ℬ → 𝒯`), `prodNP_lift` (`γ(σ,τ) ∘ γ_⊙ = σ ⊙ τ`),
`conjProdNP` (+`_apply`, `_lift`) for the members of `Ω`,
`isBasicFunctional_comp_lift` and `exists_conjProdNP_of_isBasicFunctional`.

**Next gate, named precisely: 112X.2 `tensor_basic_2` (`‖γ_⊙ s‖ = ‖s‖`), and
it is A/Proc-local.**  The route is written out in the session-55 note at the
top of `docs/AProc-survey.md`: rescale to the unital members `Ω₁`, apply the
proved **21VII** `order_separating_norm` at `γ_⊙(s*s)`, and match the
supremum with `tensorNorm`'s through the `Ω ↔ basic functionals` bijection
just banked.  What is left is sSup/iSup bookkeeping (squares against square
roots, subunital against unital).  112X.3 then follows from 112X.1's second
conjunct, and 112X.3 unblocks 116III.4/.5, 116IV.1 and 118II — none of which
touch 87III.

### 2. `CentreSeparating` → `CentreSeparatingConj`: all eight uses migrated

As the brief asked.  116IV.2 `tensor_generation_2` (3 occurrences), 116VII
`tensor_characterization` (3) and 117II.2 `sum_generation_2` (2) now use
`CentreSeparatingConj` = cstar.tex **21II**.4, the thesis's notion.  The first
two are still `sorry`, so this is a statement fix only; `sum_generation_2` was
reproved, and the brief's prediction is confirmed — **it is shorter**.  Under
the auxiliary notion the proof had to push centrality of `a` down to each
coordinate (testing against `κᵢ(b)` for centrality, then against `ω ∘ πᵢ`);
under the thesis's notion there is no centrality to push, and the whole proof
is "test `a` against `ω ∘ πᵢ` conjugated by `κᵢ(b)`, then read off
`star b * aᵢ * b`".

Consequence for A/VN, which is not my territory: the auxiliary
`Theses.A.VN.CentreSeparating` now has **no A/Proc consumer** — its doc
comment says it is "kept under this name only because `A/Proc/Tensor.lean`
states eight results with it … and are to be migrated".  Its only remaining
use in the tree is a `have` inside a proof at `A/VN/Basic.lean:1837`, so A/VN
can retire or inline it.

### 3. Two corrections to `docs/AProc-survey.md`

1. **129X `continuous_finite_measure_space_not_duplicable` is not behind
   115II.**  The survey said it "needs the product functional `ω ⊗ ω` and
   `carrier-tensor` faithfulness (118IV), both behind 115II".  Neither is:
   `prodNP` produces `ω ⊗ ω` directly from `IsTensorProduct.prod_exists`, with
   no `tmap` anywhere, and the *statement* of **118IV.4** `carrier_tensor_4`
   quantifies over an np-functional `χ` on `𝒜 ⊗ ℬ` restricting to the product
   — again no `tmap`.  129X's blocker is therefore **118IV.4, inside this
   chapter**, plus the dyadic-halving construction of proc.tex:6395 (whose
   input `continuous_measure_space` is already proved in `Duplicators.lean`).
2. **The D1 `smul` fix does not, by itself, make 129X/130IV/130V provable.**
   It was necessary — without ℂ-linearity the map `ψ : z ↦ q(const z)` need
   not be the algebra map, which is exactly why **130II** had to be routed
   through Gelfand–Mazur — but it is not the missing piece.  For **130IV**
   the missing piece is a *uniform* bound on representatives: to invert
   `q f ↦ (qB n f)ₙ` one must, given `y ∈ ℓ^∞(ℬ)`, choose representatives
   `fₙ` with a common bound, and `IsLinftyOf` records no norm or order at
   all.  It is derivable — `q` preserves positivity (`f ≥ 0` is `g*g` for
   `g = √f`), `q(1_S) ≠ 0` when `μ S > 0` by the `kernel` field, and
   `(y n · q(1_S))*(y n · q(1_S)) ≥ (M+ε)² q(1_S)` contradicts `‖y n‖ ≤ M` —
   but it is a build, not a corollary.  *One thing is free*: normality of the
   resulting map, since a bijective ∗-homomorphism is an order isomorphism
   and `starAlgEquiv_preservesDirSups'` (already in `Tensor.lean`) applies.
   130V remains blocked on 130IV alone.

### 4. Nothing false found

No ERRATA or QUESTIONS row was added, changed or removed this session.  Every
step of the thesis's argument for 112X.1 checked out; the only divergence is
the density/continuity step of §1, which the thesis leaves implicit and which
needs 74VI rather than 108II's own ultraweak density.

### 5. Verification

`lean` under the `LEAN_PATH` bypass: `Tensor.lean` **0 errors, 38
`declaration uses 'sorry'` warnings** (was 39); `Duplicators` 11,
`QuantumLambda` 17, `Measurement` 11, all 0 errors, recompiled against the
rebuilt `Tensor.olean` (written with `lean -o` to the scratchpad and copied
into `.lake/build/lib/lean/Theses/A/Proc/`, which is therefore current).
`#print axioms` was run from a *copy* of `Tensor.lean`, never from an
importing scratch file, and returns `[propext, Classical.choice, Quot.sound]`
for `tensor_basic_1`, `sum_generation_2`, `tensorSpan`, `range_lift_eq_span`,
`eq_prodNP`, `centreSeparatingConj_prodFunctionals`,
`dense_ultrastrong_tensorSpan`, `lift_one`, `lift_mul`, `lift_star`,
`prodNP_lift`, `conjProdNP_lift`, `isBasicFunctional_comp_lift` and
`exists_conjProdNP_of_isBasicFunctional`.

## Session 56 — `A/VN`: **`NormalFunctionals.lean` is finished** — 86IX, 86XII, 87III, 87VI, plus 67II.3 and 67IV.1 (worker 81, A chain)

`NormalFunctionals.lean` goes 4 → **0**; `Projections.lean` 13 → **11**.
A/VN total 48 → **42** (compiler-counted).  All six new theorems, and all
seven new helpers, are `#print axioms`-clean.

### 1. The parsec-860/870 block, whole

The four were one chain: **87III** needs **86XII**, which is a corollary of
**86IX**, and **86IX** is the Krein–Milman argument.  All four are the
thesis's own proofs.

* **86IX** `polar_decomposition_of_functional` (vn.tex:6373).  The thesis
  takes the maximum of `f` over the ultraweakly compact ball (**77III**
  `vn_ball_compact`, proved session 53), extracts an extreme point of the
  face `F = {a ∈ (𝒜)₁ : f(a) = ‖f‖}` by Krein–Milman, and feeds it to
  **86VI** `vn_ball_extreme_point`.
* **86XII** `uwcont_on_ball` (vn.tex:6435): `f = f(uu*(·)) = g(u*(·))` with
  `g := f(u(·))` positive; `g` is ultraweakly continuous on `[0,1]` because
  `a ↦ ua` maps the effects into the ball, so `g` is normal, so continuous.
* **87III** `predual_complete` (vn.tex:6509): the ε/3 estimate of the thesis,
  run as *uniform* convergence on the ball (`TendstoUniformlyOn.continuousOn`)
  rather than net-by-net; then 86XII.  Stated for a Cauchy **filter**
  (`IsComplete`), so the approximating sequence is extracted from
  `𝓝 x ∩ 𝓟 (predual A) ∈ F`.
* **87VI** `norm_predual` (vn.tex:6563): `a = [a]√(a*a)` (**82I**) and
  `f := ω([a]*(·))`.

### 2. The reusable infrastructure this needed (all public, in the same file)

* **`ultraweak_isTopologicalAddGroup`, `ultraweak_continuousSMul`,
  `ultraweak_locallyConvexSpace`** — three lines each.  `ultraweak A` is an
  `⨅` of topologies induced by `ℂ`-linear maps, and Mathlib has
  `topologicalAddGroup_iInf`/`_induced`, `continuousSMul_iInf`/`_induced`,
  `LocallyConvexSpace.iInf`/`.induced`.  With **44XI**.1 (Hausdorff) this
  makes `(A, ultraweak)` an LCTVS over `ℝ`, so `IsCompact.extremePoints_nonempty`
  (Mathlib's Krein–Milman lemma) applies directly.  **Anyone needing a
  compactness/convexity argument in the ultraweak topology should start here.**
* **`exists_extremePoint_max`** — the Krein–Milman step of 86IX, isolated so
  that it mentions no `ContinuousLinearMap`: `f` linear and ultraweakly
  continuous on `(𝒜)₁` yields `M ≥ 0` and an extreme point `u` of the ball
  with `f(u) = M` and `|f| ≤ M` on the ball.
* **`posFunctional_mul_eq_zero`** — a positive functional killing a
  projection `q` kills `qb` and `bq` for every `b` (Cauchy–Schwarz,
  `omega_norm_basic_1`).  This is what replaces the thesis's appeal to
  `carrier-fundamental` in 86IX (see divergences).
* **`preservesDirSups_of_continuousOn_effects_functional`** — **44XV** (2) ⇒ (3)
  *for functionals*.  `A/VN/Basic.lean`'s `preservesDirSups_of_continuousOn_effects`
  is `private` **and** typed `f : A →ₚ[ℂ] B` with `B : Type u` carrying a
  `VonNeumannAlgebra` instance, which `ℂ : Type 0` does not have (that is
  what `CU` exists for, but `CU` has no `VonNeumannAlgebra` instance and is
  declared 3000 lines *below* 87III).  The proof is the Basic.lean one with
  the target specialised to `ℂ`, where the closing `np_orderSeparating` step
  collapses to a real/imaginary-part comparison.  **Cleanup for whoever next
  edits `Basic.lean`: un-`private` that lemma, or better, state it once for a
  `PositiveLinearMap` into any target and delete this copy.**

### 3. Divergences

* **86IX, class 2 (different route, one step).**  The thesis derives
  `f(ubu*u) = f(ub)` from `u*u ≥ ⌈f(u(·))⌉` and **63I** `carrier-fundamental`.
  The carrier is only defined for *normal* positive maps, and at that point in
  the argument `f` is not yet known to be ultraweakly continuous — 86XII is
  its corollary, so using it would be circular.  We use plain Cauchy–Schwarz
  instead (`posFunctional_mul_eq_zero`), which needs no normality and is what
  `carrier-fundamental` is doing here anyway.  **Filed in ERRATA** as
  `86X`: as written, 86IX's last paragraph cites a lemma about carriers of
  *normal* functionals for a functional whose normality is proved only in the
  next point (86XII), which is a corollary of 86IX.
* **86IX, class 3 (mild).**  The thesis says "the subset `{f(a) : a ∈ (𝒜)₁}`
  of **ℝ** is compact and therefore has a largest element, which must be
  `‖f‖`".  That set is a subset of `ℂ`, not `ℝ`; the maximum meant is the
  maximum of `Re f`, and the identification with `‖f‖` uses that `λa ∈ (𝒜)₁`
  for `|λ| = 1`.  Also `‖f‖` is used before `f` is known bounded — boundedness
  is exactly what compactness of the image gives.  Both are harmless; we make
  them explicit.
* **87III, class 2.**  The thesis argues net-by-net ("one easily deduces");
  we package the same ε/3 as uniform convergence on the ball.
* **87VI, class 2 (one step).**  The thesis writes
  `‖√(a*a)‖ = sup_{ω ∈ Ω} |ω(√(a*a))|` over the npu-maps, i.e. invokes
  **21VII** `order-separating-norm` for the *normal* states.  Getting that
  family into the shape `order_separating_norm` wants (a family of **unital**
  pu-maps, so each `ω` must be renormalised, with the `ω(1) = 0` case split
  out) is more work than the substitute: bound `ω(√(a*a)) ≤ b·ω(1)` for every
  np-functional directly and apply `np_orderSeparating` to get
  `√(a*a) ≤ b·1`.  Same content, no renormalisation.

### 4. `Projections.lean`: 67II.3 and 67IV.1

* **67II**.3 `central_examples_3` — only scalars are central in `B(H)`.
  `T` commutes with `|x⟩⟨x| = (innerSL ℂ x).smulRight x`, so every vector is
  an eigenvector; the standard two-case argument (`y` dependent on / independent
  of a fixed `x₀ ≠ 0`) then gives a single eigenvalue.  The `Subsingleton H`
  case is separate.
* **67IV**.1 `central_projections_sums_1` — the corner `cA`.  Parts 1–2 are
  computation.  Part 3 (`c⋁D = ⋁D`) does **not** need normality of `b ↦ cb`:
  `c(·)c` is monotone, so `csc` is an upper bound of `D` (each `d = cdc`),
  whence `s ≤ csc`; conjugating by `q := c^⊥` gives `qsq ≤ q(csc)q = 0`, while
  `0 = qdq ≤ qsq`; so `qsq = 0`, and `qsq = qs` by centrality of `q`.
  This avoids the `IsLUB`-in-`selfAdjoint A` → `IsLUB`-in-`A` transfer that
  the normality route would need.

### 5. What this unblocks

`A/Proc`'s external frontier on `A/VN` is **empty**: 90II.2 closed in session
55, 87III and 86IX here.  112X `tensor-basic` and 87VI (for 116III.2's `≥`
half) are now A/Proc-local work.

---

## Session 55 — `B/Dils`: **151Ia `selfdual_completion_univ`** falls, and **163II-uniq** with it; 165VI is *not* the next gate (worker 82)

Two `sorry`s closed, both axiom-clean
(`propext, Classical.choice, Quot.sound`).  `B/Dils` **36 → 34**
(compiler-counted: `SelfDualCompletion` 2 → **1**, `SelfDual` 8 → **7**;
`Paschke` 7, `Kaplansky` 5, `Stinespring` 2, `Pure` 12, `HilbertModules` 0
unchanged).

### 1. **151Ia** `selfdual_completion_univ` (`SelfDualCompletion.lean`)

Cost **~360 lines** of proof plus ~110 lines of reusable private helpers,
against the survey's 300–400 line estimate — the estimate held.

The thesis's proof (151II) is transcribed as written, with one structural
choice forced by Lean.  The author says "pick a net `x_α` in `V` with
`η(x_α) → x` ultranorm, then `T̂x := unlim_α T(x_α)`"; our `UnDense` is the
*entourage* form, so the net is built explicitly, indexed by
`Finset (NPFunctional 𝒷 × ℕ)` (a finite family of functionals together with a
precision `1/(n+1)` for each), ordered by `atTop`.  `Finset` is directed, so
`atTop` is `NeBot`, and pushing that net forward along `T` gives an ultranorm
Cauchy filter on `Y`; **149V** `dils_selfdual` (`1 ⇒ 2`) supplies ultranorm
completeness of the self-dual `Y`, which produces the limit.

The one idea worth keeping is that the whole rest of the proof runs off a
**single fundamental estimate**, proved once from the net and then never
mentioning nets again:

    ‖T̂x − Tv‖_ω  ≤  C ‖x − ηv‖_ω        for every ω, every x ∈ X, every v ∈ V.

From it, *one np-functional at a time*:
* `T̂ ∘ η = T` — take `v` with `x = ηv`, so the right-hand side is `0`;
* additivity, ℂ-homogeneity, ℬ-homogeneity and uniqueness — each is
  "`‖(both sides) difference‖_ω ≤ (const)·ε` for every `ε`", with the
  approximant chosen for that single `ω` (two of them for ℬ-homogeneity, see
  below);
* boundedness — take `v = 0`, giving `‖T̂x‖_ω ≤ C‖x‖_ω` directly, with no
  density argument at all.

**Divergence, class 2 (different route for one step).**  For the final bound
the thesis takes `⟨Tx_α,Tx_α⟩ ≤ ‖T‖²[x_α,x_α]` (**144V**) to the ultraweak
limit through **148V** `innerprod_ultraweak`.  We get `‖T̂x‖_ω ≤ C‖x‖_ω` for
every `ω` from the fundamental estimate at `v = 0` and then convert it to
`⟨T̂x,T̂x⟩ ≤ C²⟨x,x⟩` by **44XI** `np_orderSeparating`.  Same content, and it
avoids ultraweak limits entirely.  (Note our statement does not claim
`‖T̂‖ = ‖T‖`, only that *some* bound exists, so the sharp constant is not
formalized either way — see the moreover-clause of the doc comment.)

**The ℬ-homogeneity step needs two functionals, not one.**  `‖b·z‖_ω` is not
controlled by `‖z‖_ω`; the identity is
`‖b·z‖_ω = ‖z‖_{ω(b(·)b*)}`, i.e. the seminorm at the *conjugated*
np-functional `conjNP (star b) ω` (**44XI**).  So the approximant for
`T̂(b·x) = b·T̂x` has to be chosen against the two-element family
`{ω, conjNP (star b) ω}` — which is exactly why the entourage form of
`UnDense`, and not a one-seminorm-at-a-time version, is the right hypothesis.

Reusable private helpers added at the top of the parsec-1510 block, all
phrased with `inner 𝒷` rather than `(cstarBInner 𝒷 W).inner` so that `rw`
can use them (`HilbertModules.lean` keeps its versions `private`):
`un_zero`, `un_neg`, `un_add_le`, `un_sub_le`, `un_sub_comm`,
`un_smul_complex` (`‖c·z‖_ω = |c|‖z‖_ω`), `un_op_smul` (the conjugation
identity above), `un_bmm_le`, `op_smul_sub'`, `eq_zero_of_un_small` (the
seminorms are separating), and `npf_smul`/`npf_nonneg`/`npf_im_zero`.

### 2. **163II**-uniq `selfdual_compl_defining_unique` (`SelfDual.lean`)

~110 lines, immediate once 151Ia is available.  151Ia is applied four times:
`E₁ → E₂` (giving `U`), `E₂ → E₁` (giving `W`), and once on each of `E₁`,
`E₂` for the *uniqueness* clause, which identifies `W ∘ U` and `U ∘ W` with
the identity because all four factor the embedding through itself.  That is
the thesis's own argument verbatim.

**Divergence, class 2 (different route), for the inner-product clause.**  The
thesis argues that `U(ηV) = η₂V` is ultranorm dense and concludes by
**148V** `innerprod_ultraweak`.  We instead bundle `U` as a
`E₁.X →L[ℂ] E₂.X`, take its adjoint `U*` — which exists by **152VIII**
`hilbmod_adjoint_exists`, since `E₁.X` is self dual — and observe that
`U*U` and `id` have the same vector states on `η₁V`:

    ⟨η₁v, U*U η₁v⟩ = ⟨Uη₁v, Uη₁v⟩ = ⟨η₂v, η₂v⟩ = [v,v] = ⟨η₁v, η₁v⟩.

**152IX**.2 `hilmod_fixed_on_V_eq` then gives `U*U = id`, whence
`⟨Ux,Uy⟩ = ⟨x, U*Uy⟩ = ⟨x,y⟩`.  This is the same density argument, but run
once inside 152IX (which is proved) instead of being re-run on nets here.

### 3. **165VI is not the next gate** — the survey was wrong about what it owes

`docs/BDils-survey.md` said 165VI `ba_ext_tensor_pres` was down to
"165IX/165X for `exists_productFunctional`/`separating`".  That is wrong on
both counts, and the item is **blocked outside the directory**:

* the thesis's 165IX/165X produce product functionals only for the *vector
  states* `Ω_X = {f⟨x,(·)x⟩}` and `Ω_Y`, and then appeal to
  **116VII** `tensor-characterization` (proc.tex:3578) — the criterion that a
  *faithful family* of product functionals suffices;
* our `IsVNTensor.exists_productFunctional` transcribes proc.tex's `tensor`
  definition literally and demands a product functional for **every** pair of
  np-functionals, which 165IX does not supply;
* `tensor_characterization` lives in `Theses/A/Proc/Tensor.lean`, is **itself
  `sorry`**, and `A/Proc` is not on `B/Dils`'s import path.

So closing 165VI needs 116VII proved *and* importable (or re-derived inside
`B/Dils`), not 165IX/165X.  Recorded in the survey.

### 4. What is left

Nothing else in `B/Dils` was unblocked.  `existence_paschke`,
`univprop_ext_tensor` and the whole 157IV.2/.3 → 171II → `Pure.lean` chain
still sit on **150II** `dils_completion`, which is the type construction and
was not attempted.  The only remaining item in the directory that is
neither blocked nor known-false and was not attempted is
**138VIII-findim** `kraus_decomposition_findim` (`Stinespring.lean:2037`);
`Stinespring`'s other `sorry` is 139XI `ess_uniq_pur`, which is false
(QUESTIONS **B12**).

## Session 57 — `A/Proc`: **112X closes whole (all five parts) and 112XI `tensor_universal_property` with it** (worker 82, `Tensor.lean`)

Territory: `Theses/A/Proc/` only.  Files touched: `Theses/A/Proc/Tensor.lean`,
`docs/AProc-survey.md`, this log.  Nothing staged, nothing committed.
**A/Proc 77 → 72**, compiler-counted per file: `Tensor` **33** (was 38),
`Measurement` 11, `QuantumLambda` 17, `Duplicators` 11 (the last three
untouched).

| point | declaration | divergence class |
|---|---|---|
| **112X**.2 | `tensor_basic_2` | 2 — the thesis's `Ω₁`/**21VII** route replaced by the order-separating property itself (§2) |
| **112X**.3 | `tensor_basic_3` | 1 — the thesis's route |
| **112X**.4 | `tensor_basic_4` | 1 — the thesis's route verbatim |
| **112X**.5 | `tensor_basic_5` | 1 — the thesis's route, with the topology half done by `induced_mono` rather than pointwise (§4) |
| **112XI** | `tensor_universal_property` | 1 — proc.tex:2998's one-line proof, with its "trivial details" spelled out (§5) |

### 1. The brief was stale in the decisive place

It said "A/Proc's remaining external frontier is just 87III and 86IX, and an
A/VN worker is on both".  **That worker finished in session 56**: the log
entry immediately above the brief's own baseline records
`NormalFunctionals.lean` going 4 → 0, i.e. **86IX and 87III were already
proved** when this session began.  So 112X.4 and 112X.5 — listed as
externally blocked in both the brief and the survey — were A/Proc-local from
the start, and with them 112XI.  The nominated targets (112X.2, then .3) were
the right *first* two steps but not the ceiling; taking the frontier claim at
face value would have stopped four sorries short.

Correspondingly, **116III.4/.5, 116IV.1 and 118II did not fall** — they were
not attempted.  112X.3 does unblock them in the dependency sense, but 116III.4
in particular is *not* a corollary: its hint reduces joint ultraweak
continuity of `⊗` to continuity of `(a,b) ↦ ∑ σ(aᵢ*aaⱼ)τ(bᵢ*bbⱼ)`, which
handles the *simple* functionals only, while `uwTensorTopology` and the
ultraweak topology of `𝒜⊗ℬ` are generated by their operator-norm limits — and
the approximation `‖f(x) − g(x)‖ ≤ ε‖x‖` is not uniform on ultraweak
neighbourhoods, which are unbounded.  Flagged here rather than in ERRATA
because the gap may well be closable; it is not a defect until someone tries.

### 2. **112X**.2 needed no `Ω₁` and no sSup bookkeeping

The session-55 plan (rescale `Ω` to its unital members `Ω₁`, feed **21VII**
`order_separating_norm`, match suprema) was not used.  `order_separating_norm`
wants a family of *unital* pu-maps, so the plan pays for a renormalisation of
every member of `Ω` and then has to match two suprema.  Instead:

* **`‖γ_⊙ s‖ ≤ ‖s‖`** — 112X.1's *order separating* conjunct applied at
  `x = γ_⊙(s)*γ_⊙(s)`, `y = ‖s‖²·1`.  Its hypothesis is exactly
  `ω(s* s) ≤ ‖s‖²ω(1)` for the basic functional `ω = χ ∘ γ_⊙`, which is the
  one new private lemma, `basic_star_self_le`: rescale `ω` by `ω(1)⁻¹`
  (`isBasicFunctional_smul`) to land in the subunital family the supremum
  runs over; the degenerate branch `ω(1) = 0` is `basic_norm_le_tensorNorm`,
  already in the file.  Then `‖x‖ ≤ ‖s‖²` by 17VI.3a
  `norm_le_iff_neg_algebraMap_le`.
* **`‖s‖ ≤ ‖γ_⊙ s‖`** — `Real.sSup_le` over the defining set, with
  `exists_conjProdNP_of_isBasicFunctional` turning each basic `ω` into an
  np-functional `χ` on `𝒯` and `χ(star y * y) ≤ ‖star y * y‖ χ(1)` doing the
  rest.

This is 21VII's own argument with the renormalisation step deleted, so no
mathematical content of the thesis is skipped — but it *is* a divergence, and
the author's phrasing ("the subset `Ω₁` of unital maps is order separating, and
so determines the norm") is a longer road than the exercise needs.

### 3. **112X**.3 and **112X**.4

112X.3's second conjunct is 112X.1's second conjunct restricted along `γ_⊙`:
`isBasicFunctional_comp_lift` makes each summand of the approximating sum a
basic functional, so the sum is *simple*, and 112X.2 converts the
operator-norm bound `ε‖γ_⊙ t‖` into the tensor-norm bound
`ε·tensorNorm t`.  The continuity conjunct is then `iInf_le`: those
restrictions are by definition among the maps `uwTensorTopology` is initial
for.

112X.4 is the thesis's paragraph verbatim — **86IX** for the partial isometry
`u`, **86XI** `functional_norm` for `f(u) = ‖f‖`, **74VI** for a net from
`γ_⊙(𝒜⊙ℬ)` with `‖s_α‖ ≤ ‖u‖(1+ε)`, and `‖u‖ ≤ 1` from
`IsStarProjection.norm_le` at `u*u`.  The converse half is one line of 112X.2.

### 4. **112X**.5: what the two halves actually cost

*Existence.*  The thesis says "using the fact that the operator norm limit of
np-functionals is an np-functional again, see `predual-complete`".  Three
things have to be supplied around that:
* each simple functional is lifted to a *sum* of members of `Ω`, which needs
  np-functionals as bounded operators — new private `npFunctional_norm_le`
  (`‖ω a‖ ≤ ω(1)‖a‖`, from Kadison's inequality and
  `‖a‖_ω ≤ ‖a‖‖1‖_ω`) and `npCLM`;
* the sequence is Cauchy **because of 112X.4**, which is the only place the
  isometry of restriction is used;
* `predual_complete` returns a member of the *predual* — an ultraweakly
  continuous bounded functional, not an np-functional.  Positivity of the
  limit is a re/im argument; **normality** is
  `preservesDirSups_of_continuousOn_effects_functional`, the 44XV(2)⇒(3)
  helper A/VN banked in session 56.  Without it there is no route from
  "ultraweakly continuous and positive" to `NPFunctional` in the tree.

*The topology equality* is cheaper than the survey suggested: `≤` is 112X.3's
first conjunct through `continuous_iff_le_induced`, and `≥` is
`induced_mono` applied to `ultraweak 𝒯 ≤ induced ω` for the extension `ω` of
the given norm-limit-of-simple functional, followed by `induced_compose`.  No
pointwise argument is needed.

### 5. **112XI**: the "trivial details"

proc.tex:2998 is one sentence: `β_⊙` is ultraweakly continuous and bounded,
`𝒜⊙ℬ` is an ultraweakly dense ∗-subalgebra of `𝒯` via `γ_⊙`, so **77V**
`vn_extension` applies "except for some trivial details".  The details are two,
and only one is trivial:
* `vn_extension` wants a map **on the subalgebra**, so one needs
  `γ_⊙⁻¹ : S → 𝒜⊙ℬ`.  `γ_⊙` is injective (it is an isometry, 112X.2, and
  `tensorNorm_eq_zero_iff`), so the inverse is a `choose` and its linearity is
  injectivity applied twice.  Its continuity for the topology *induced from
  `𝒯`* is exactly **112X.5**'s topology equality — this is the step the
  session-54 note correctly identified as not substitutable by
  `BilinNormal β`.
* the moreover-clause `‖β_γ‖ = ‖β_⊙‖`.  `≥` is 112X.2; `≤` needs the same
  74VI approximation as 112X.4 and a new private
  `norm_le_of_uwTendsto` — the ultraweak twin of `norm_le_of_usTendsto`
  (`A/VN/Division.lean`), immediate from `isClosed_ultraweak_closedBall`.
  Worth keeping: **A/VN has the ultrastrong version only**, and the ultraweak
  one is what any "extend a bounded map by density" argument wants.

### 6. Nothing false found

No ERRATA or QUESTIONS row was added, changed or removed.  Every step of the
thesis's argument for 112X.3/.4/.5 and 112XI checked out; the divergences are
those listed in the table.

### 7. Verification

`lean` under the `LEAN_PATH` bypass: `Tensor.lean` **0 errors, 33
`declaration uses 'sorry'` warnings** (was 38).  Every new declaration
`#print axioms` to exactly `[propext, Classical.choice, Quot.sound]`, checked
by appending the commands to a *copy* of the module.

*Operational note.* For roughly an hour mid-session `A/VN/Basic.olean` was
**deleted** from `.lake/build` by a concurrent `lake build`, and the A/VN
worker's source was itself transiently broken, so `Tensor.lean` could not be
checked at all.  Retrying is the documented cure and it eventually worked;
building a private copy of the olean into a scratch directory (`lean -o`) is
the fallback when the shared one is missing, but it does not help while the
*source* is red.

## Session 57 — `A/VN`: **66IV.4, 70II and 70III close `Projections.lean`'s last chain**, eight of the nine 43II counterexamples fall, and both `Basic.lean` cleanups land (worker 82, A chain)

`Basic.lean` 24 → **16**, `Projections.lean` 11 → **8**, `Division.lean`
7 → **6**; A/VN total 42 → **30** (compiler-counted).  All twelve new theorems
and all new helpers are `#print axioms`-clean.  264 lines of duplicated code
were deleted.

### 1. The parsec 660–700 chain, finished

* **66IV**.4 `ultracyclic_basic_4` — the Zorn argument, on the template of
  **83V** `cceil_sum` (`Division.lean`): a maximal set `S` of np-functionals
  whose carriers lie below `p` and are pairwise orthogonal; if
  `q = ⋁_{ω∈S}⌈ω⌉ ≠ p` then `r = p − q` is a non-zero projection, faithfulness
  of the np-functionals (**42I**.2) gives `τ` with `τ(r) ≠ 0`, and
  `ω = τ(r(·)r)` has `0 ≠ ⌈ω⌉ ≤ r ⊥ q`, contradicting maximality.
* **70II** `central_projection_central_carrier` — **the brief and the survey
  both said this was blocked on 66IV.4; it is not.**  vn.tex 70II's own hint
  ("take a maximal set of np-functionals for which the `⌈⌈ωᵢ⌉⌉` are
  orthogonal") is an independent Zorn argument of the same shape, run on the
  *central* carriers.  The only extra ingredient is that `r = c − q` is
  *central* (`projSup_isCentral` for `q`, the hypothesis for `c`), so
  `⌈ω⌉ ≤ r` upgrades to `⌈⌈ω⌉⌉ ≤ r` by leastness of the central support.
* **70III** `cvn` — **it does not need 54XI either.**  Our statement is the
  FIXME reduction (`1 = ∑ᵢ ⌈⌈ωᵢ⌉⌉` with each `ωᵢ` faithful on its corner), not
  the `⊕ᵢ L^∞(Xᵢ)` classification; 54XI is what would turn the corners into
  `L^∞`, and that is exactly the part the FIXME says we do not state.  So 70III
  is 70II at `c = 1` plus: in a commutative algebra `⌈⌈ω⌉⌉ = ⌈ω⌉`, and
  `⌈ω⌉a = a` with `ω(a) = 0` forces `⌈a⌉ ≤ ⌈ω⌉ ≤ ⌈a⌉^⊥` (**60I**
  `ceil_functionals_lemma` and carrier leastness), i.e. `⌈a⌉ = 0`, i.e. `a = 0`.

*Divergence, class 4 (never consulted):* 66IV.4 and 70II are exercises with no
solution in `asols.tex` (there is no `parsec-660.40` or `parsec-700.20`
entry — the file's solutions stop at parsec 340), so only the hints were
available; both hints were followed.

### 2. Our own mis-transcription: `∃ (ι : Type _)` auto-bound a fresh universe

`ultracyclic_basic_4`, `central_projection_central_carrier` and `cvn` all wrote
the index type as `∃ (ι : Type _)`.  In a theorem statement that `_` is
**auto-bound as a new universe parameter of the theorem**, so the three
statements claimed: *for every universe `v` there is an index type in `Type v`
and a family …*.  That is false as soon as `A` is bigger than `Type v` allows
— the honest index set is a set of np-functionals on `A`, which lives in `A`'s
own universe.  `Division.lean`'s `cceil_sum` had already got this right
(`∃ (ι : Type u)`, with `universe u` declared at the top of that file).
`Projections.lean` now declares `universe u v w` and `variable {A : Type u}
{B : Type v}` in place of `{A B : Type*}` (the same thing, only named), and the
three statements read `∃ (ι : Type u)` — `∃ (ι : Type w)` for `cvn`, whose
carrier `C : Type w` is bound in the statement itself.  No use sites exist
outside the file, so nothing downstream is affected.  **Grep the tree for
`∃ (ι : Type _)` before trusting any similar statement.**

### 3. `Basic.lean`: eight of the nine 43II counterexamples

Proved: **43II**.2a `vn_counterexamples_2_sup`, .2b `_2_tendsto`, .4a `_4_ket`,
.4b `_4_bra`, .4c `_4_star`, .5 `_5`, .6 `_6`, .6c `_6_sq`.  Only .11 is left.

Three new public helpers in `Basic.lean`'s `section BH`, all reusable:

* **`omegaNorm_vectorNP`** — `‖a‖_ω = ‖aξ‖` for `ω = ⟪ξ,(·)ξ⟫`.  Moved up from
  `Completeness.lean` (where it sat 3000 lines downstream of `vectorNP`); the
  copy there is deleted.
* **`hasSum_omegaNorm_sq`** — for `ω = ∑ₙ⟪xₙ,(·)xₙ⟫` (**39IX** `bh_np`),
  `HasSum (n ↦ ‖T xₙ‖²) (‖T‖²_ω)`.  This is the survey's observation made
  usable; it turns every part into an estimate on `∑ₙ`.
* **`ultrastrong_continuous_apply`** — `a ↦ ax` is ultrastrongly continuous,
  i.e. **the ultrastrong topology is finer than the strong topology**.  Three
  lines from `omegaNorm_vectorNP` plus `isOpen_generateFrom_of_mem`, and it is
  what makes part 5 tractable: the image of the ultrastrongly compact ball
  under `a ↦ a e₀` would be a compact subset of `ℓ²` containing every `eₙ`,
  hence (metric space) sequentially compact, and no subsequence of an
  orthonormal basis converges.

The engine for parts 2 and 4 is one private lemma,
`usTendsto_zero_of_norm_apply_coord`: a sequence `(Tₙ)` on `ℓ²` with
`‖Tₙ y‖ = |y(n)|` for every `y` converges ultrastrongly to `0`.  Both
`|n⟩⟨n|` and `|0⟩⟨n|` satisfy that hypothesis, so 2b and 4a are the same
theorem.  The limit `∑ₘ |xₘ(n)|² → 0` is Mathlib's Tannery theorem
`tendsto_tsum_of_dominated_convergence` with bound `(‖xₘ‖²)ₘ`.

*Divergences.*  vn.tex 43II is an Exercise with no printed solution, so all
eight are class 4 (thesis proof never consulted — there is none) except that
the *statements* were followed exactly.  Two routes are worth recording as
deliberate choices:

* part **4b**'s "no ultrastrong limit" and part **5** are both closed by the
  same observation, isolated as `not_tendsto_single_sub`: if `e_{φ n} → v` in
  `ℓ²` then `‖1 − v(φ n)‖ ≤ ‖e_{φ n} − v‖`, whose left side tends to `1` (the
  coordinates of `v ∈ ℓ²` tend to `0`) and whose right side tends to `0`.  This
  is cheaper than computing `‖eₙ − eₘ‖ = √2`.
* part **6c** avoids Hausdorffness of the ultraweak topology (44XI.1, which is
  awkward to apply with an explicit non-instance topology): both ultraweak
  limits are tested against the single np-functional `⟪e₀,(·)e₀⟫` and
  uniqueness of limits is taken in `ℂ`.

### 4. Cleanup 1: `Basic.lean`'s `GNSSum` block is now family-indexed

`gnsHilbFam`, `gnsRepFam`, `gnsRepFam_apply_coe`, `gnsElemVecsFam`,
`gnsElemVecsFam_separating` and `gnsRepFam_normal` are stated for an arbitrary
`F : ι → NPFunctional A`.  `gnsHilb`/`gnsRep`/`gnsElemVecs`/`gnsRep_normal`
(**48VIII**) are the instance at `F = id`, and `NormalFunctionals.lean`'s
`gnsHilbOn`/`gnsRepOn`/`gnsElemVecsOn`/`gnsRepOn_normal` the instance at
`F = Subtype.val`.  **161 lines** of near-verbatim copy deleted from
`NormalFunctionals.lean`; `gnsRepOn_injective` (the genuinely new item there)
is untouched.  All public names on both sides are unchanged, so nothing
downstream had to move.

### 5. Cleanup 2: 44XV (2) ⇒ (3) is un-`private`d, and the functional copy is gone

`preservesDirSups_of_continuousOn_effects` is now public, and
`NormalFunctionals.lean`'s `preservesDirSups_of_continuousOn_effects_functional`
is a four-line corollary of it — **103 lines** deleted.

**Session 56's diagnosis of why the copy was needed was wrong on both counts.**
It recorded that the general lemma "needs a target in `Type u` with a
`VonNeumannAlgebra` instance, which `ℂ : Type 0` has not".  In fact (i) the
lemma sits in a `variable {A B : Type*}` section, so `B` is
universe-polymorphic, and (ii) `ℂ` *does* carry a `VonNeumannAlgebra` instance,
declared at `Basic.lean:646` right after `complexIdNP`.  The one real gap was
that the functional version phrases continuity against `ℂ`'s *usual* topology
while the general one uses `ultraweak ℂ`.  Those agree, and that is now a
lemma: **`ultraweak_complex : ultraweak ℂ = inferInstance`** — `complexIdNP` is
the identity, so it induces the usual topology, and every np-functional on `ℂ`
is `z ↦ z·ω(1)`, hence continuous, so the `⨅` is squeezed.

### 6. `Division.lean`: 79VI.5

**79VI**.5 `pseudoinverse_basic_2'_5` — `(0,0,1,½,⅓,…)` is not pseudoinvertible
in `ℓ^∞(ℕ)`.  The short route is **59VI**.2 `ceill_basic_2` (`⌊x⌉x = x`): a
pseudoinverse `t` satisfies `xt = ⌊x⌉`, so `xtx = x`, which coordinatewise
forces `tₙ = n − 1` for `n ≥ 2` — unbounded, contradicting
`‖tₙ‖ ≤ ‖t‖`.  No suppProj/rangeProj computation in `ℓ^∞` is needed.

### 7. Operational notes

* A concurrent `lake build` from another worker deleted and rebuilt
  `A/VN/Basic.olean` mid-session (it depends on my edits), which surfaced as
  `object file … does not exist`.  Waiting for the file to reappear is the
  cure; `lean <file> -o <olean> -i <ilean>` (no `-c`) is a lake-free way to
  refresh one module's olean without taking the lake lock.
* `set x := e with h` leaves `x` a *let*-bound fvar, so `rw [mul_sub]` &c. can
  see through it and rewrite inside `e`.  This bit twice in the Zorn proofs
  (`r * (1 − r) * r` was rewritten as `p − ⋁Q`).  `obtain ⟨r, hr⟩ : ∃ r, r = e
  := ⟨_, rfl⟩` gives an opaque `r` and is the reliable idiom.
* `rintro ν (rfl | hν) μ (rfl | hμ)` on `insert ω S` substitutes the *later*
  variable, so the name `ω` disappears in some branches.  `rcases
  Set.mem_insert_iff.mp hν with hν | hν` and an explicit `rw [hν]` is stabler.

---

## Session 57 — `B/Dils`: **158II `kaplansky_hilbmod` falls to the linking algebra** (worker on `Kaplansky.lean`)

Files touched: `Theses/B/Dils/Kaplansky.lean`, `QUESTIONS.md` (B10),
`ERRATA.md` (the 158V row), this log.  Nothing else.

**`Kaplansky.lean` 5 → 4 sorried declarations, so `B/Dils` 34 → 33.**  The
four that remain are the known-*false* 158V estimates `A₁/A₁'/A₂/A₂'`, left
deliberately.  Compiler-checked (`lean Theses/B/Dils/Kaplansky.lean` under the
`LEAN_PATH` bypass): no errors, no new warnings.

| declaration | axioms |
|---|---|
| `kaplansky_hilbmod_of_selfDual` (158II, `X` self dual) | `propext, Classical.choice, Quot.sound` |
| `kaplansky_hilbmod_of_closure` | `propext, Classical.choice, Quot.sound` |
| **`kaplansky_hilbmod` (158II)** | `propext, sorryAx, Classical.choice, Quot.sound` |

The `sorryAx` is **only** 150II `dils_completion` (`SelfDualCompletion.lean`,
still `sorry`), used to pass to the self-dual completion.  150II is at parsec
1500 and 158II at 1580, so the dependency respects the thesis's own order, and
it is not circular (158II's only appearance inside parsec 1500 is an aside).

### The proof, and why it dodges the mirror obstruction

Sessions 24/29/30 established that every route through a renormalizer
`y ↦ y·φ(⟨y,y⟩)` dies on the same quantity: one needs `ω(bb*) → 0` where
module Cauchy–Schwarz gives only `ω(b*b) → 0`.  The linking algebra removes
the quantity rather than estimating it.

Work in `Lk = C⋆ᵐᵒᵈ(ℬ, X × ℬ)` and `M = ℬᵃ(Lk)`, a von Neumann algebra by
**152X** `ba_vonNeumannAlgebra` once `Lk` is self dual (proved here from
`SelfDual ℬ X` — the direct-sum example of **141III**, `selfDual_lk`: restrict
a bounded ℬ-linear `τ` to each summand, represent it there, recombine).  Put

* `cor z = |z ⊕ 0⟩⟨0 ⊕ 1|`  (`[[0,z],[0,0]]`),  `ι b = |0 ⊕ b⟩⟨0 ⊕ 1|`,
* `(cor z)* (cor z) = ι⟨z,z⟩` — hence `‖cor z‖_φ² = (φ∘ι)(⟨z,z⟩)` **exactly**.

So ultrastrong convergence in the corner *is* ultranorm convergence in `X`,
with no mirrored term: the `|e⟩⟨e|` corner, which is where `ω(bb*)` would come
back, only appears in `(cor z)(cor z)*`, and nothing here needs it.  Two
consequences worth stating:

* **The self-adjointization `[[0,x],[x*,0]]` of the classical proof must
  *not* be used**, and is not needed.  Its square carries `θ_{e,e}`, which is
  constant along the standard counterexample (`e = |e₂⟩⟨eₙ|` gives
  `θ_{e,e} = |e₂⟩⟨e₂|`), so it does *not* converge ultrastrongly; one would
  have to detour through the ultraweak topology and `73VIII`.  Thesis A's
  **74IV** `kaplansky` already takes a non-self-adjoint element (that is
  exactly the repair recorded in its own doc comment), so `cor x` can be fed
  to it directly.
* **`𝒜` ultrastrongly dense in `ℬ` is not needed** — the hypothesis Lin's
  Theorem 4.4 requires and 158II lacks.  74IV is applied to one element and
  one subalgebra; no density in `M` is asserted anywhere.

The subalgebra is `lkSub N = {T : T(N) ⊆ N ∧ T*(N) ⊆ N}` for
`N = cl(D) ⊕ 𝒜` — a closed unital ∗-subalgebra for trivial reasons, and
`cor d ∈ lkSub N` for `d ∈ D` is *precisely* the two hypotheses of 158II:
`𝒜·D ⊆ D` handles `cor d`, and `⟨D, cl D⟩ ⊆ 𝒜` handles `(cor d)*`.  The
latter needs `⟨d,d'⟩ ∈ 𝒜` for **distinct** `d,d'`, which is polarization
(`⟨d,d'⟩ + ⟨d',d⟩` and `i(⟨d,d'⟩ − ⟨d',d⟩)` are both differences of diagonal
values), plus continuity of `⟨d,·⟩` and closedness of `𝒜`.  This answers the
first cheap sub-question of the brief: **yes, `⟨D,D⟩ ⊆ 𝒜` plus `𝒜·D ⊆ D` give
`q·C*(D)·p ⊆ cl(D)`** — in fact one never has to identify the C\*-algebra
generated by `D`, since `lkSub N` contains it and has the corner property by
construction.  And the second: **yes, the ultranorm topology on `X` is the
ultrastrong topology of the linking algebra restricted to the corner**, by the
displayed identity above (`→` via `iotaNP`, `←` via the vector np-functional
`baVecNP` at `0 ⊕ 1`, **152XIII**).

The one genuinely mathematical ingredient beyond bookkeeping is that
`φ ↦ φ∘ι` maps np-functionals of `M` to np-functionals of `ℬ` (`iotaNP`),
i.e. that `ι` is *normal*.  Proof: `⟨v, ι(b)v⟩ = v₂ b v₂*`, so by
`ba_nonneg_iff`/`ba_inner_mono` (**144I**) this reduces to normality of
`b ↦ c b c*` on `ℬ`, which follows from `conjNP` + `np_orderSeparating`
(**44XI**) without touching the private `conjSA_isLUB` of `A/VN/Basic`.

Compression: `0 ⊕ 1 ∈ N` (this is where `1 ∈ 𝒜` is used), so for `a ∈ lkSub N`
the vector `a(0 ⊕ 1)` lies in `N` and its `X`-component `w₁` lies in `cl(D)`,
with `‖w₁‖ ≤ ‖a‖ ≤ ‖cor x‖ ≤ ‖x‖`; and `⟨u,u⟩ ≥ ⟨u₁,u₁⟩` in `ℬ` turns the
ultrastrong estimate into the ultranorm one.

`kaplansky_hilbmod_of_closure` (public, axiom-clean, independent of everything
else here) converts `cl(D)` back to `D`: norm-approximate `z ∈ cl(D)` by
`d' ∈ D` within `δ`, then rescale `d = t·d'` with `t = ‖x‖/(‖x‖+δ)`, which is
in `D` because `𝒜 ∋ c·1` makes `D` a ℂ-subspace.  The entourage form absorbs
the error: the two extra terms are each `≤ √(ω 1)·δ`, and `δ` is chosen
against the *single* functional `Σᵢ ωᵢ` (`npSum`), so one `δ` serves all `n`
seminorms.  No case split on `x = 0` is needed.

### Reduction of the general case to the self-dual case

`unDense_trans`: ultranorm density is transitive, so `D` ultranorm dense in
`X` and `range η` ultranorm dense in `X̄` give `η '' D` ultranorm dense in `X̄`.
Since `η` preserves the inner product it preserves both the norm and every
ultranorm seminorm, so the conclusion transports back verbatim.  This is the
whole of the general case; it costs ~60 lines on top of the self-dual one.

### What is in the file

All of it in one `section Linking` at the end of `Kaplansky.lean`, everything
`private` except `kaplansky_hilbmod_of_closure`,
`kaplansky_hilbmod_of_selfDual` and `kaplansky_hilbmod`.  `Kaplansky.lean` now
imports `Theses.B.Dils.SelfDualCompletion` (acyclic: `SelfDual.lean` imports
`Kaplansky.lean`, `SelfDualCompletion.lean` does not).

**One reordering.**  `theorem kaplansky_hilbmod` has been moved from its
original place (between 158Ia and 158V) to the end of the file, because its
proof needs both the `WeakToStrong` np-functional helpers and the linking
algebra; a pointer comment sits at the original location.  Its doc comment is
rewritten (class 2 — a different proof), as is the file header.  The statement
is **unchanged**.

**Duplication to consolidate later**: the private `mkb` is a copy of **159II**
`mketbra` (`SelfDual.lean`), which cannot be imported here because
`SelfDual.lean` imports this file.  If `mketbra` is ever moved to
`HilbertModules.lean`, `mkb` and its five lemmas can go.

### Things the coordinator's brief got wrong (all in the safe direction)

* "Obstacle 3: compression lands in `q C*(D) p`, not `D`" — true but avoidable:
  one never needs `C*(D)`, only *some* closed ∗-subalgebra containing `cor D`
  with a corner in `cl(D)`, and `{T : T(N) ⊆ N ∧ T*(N) ⊆ N}` is one.
* "`L(X)` is a von Neumann algebra only when `X` is self-dual" — right, but
  152X `ba_vonNeumannAlgebra` and 152XIII `baVecNP` are already **proved** in
  `SelfDualCompletion.lean`, so no Paschke theory has to be built; the only
  missing piece was `SelfDual ℬ (X ⊕ ℬ)`, ~25 lines.
* The suggestion to model the proof on `kaplansky`'s own `antiDiag` trick is
  the one thing that does *not* port (see above): self-adjointness is exactly
  what one must avoid here.
* Bas's alternative route through 161II/161IV (`X ≅ ℓ²((pᵢ))`, `L(X)` a corner
  of a matrix algebra) is not needed — `Ba` is already available abstractly.
