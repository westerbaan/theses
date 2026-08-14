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
- **177Ia** `Theses/B/Eff/EffectAlgebras.lean:959` (`ea_modularity_prop`) — the
  proof (eff.tex:492) reduces to a lemma about `(x ⊖ c) ∧ (x ⊖ d)` and uses
  that `z ↦ zᵖ` is an order anti-isomorphism to turn infima into suprema.  That
  transfer, together with `x ⊖ c = (xᵖ ⋁ c)ᵖ`, has to be built on top of the
  ad-hoc `PCM.IsInf`/`PCM.IsSup` predicates; not attempted for lack of time.
- **177VI** `Theses/B/Eff/EffectAlgebras.lean:1045` (`orth_ea_is_orthomodular`)
  — depends on 177Ia (parked) *and* on an auxiliary distributivity claim that
  eff.tex:578 only gestures at ("Similar to `modularity-lemma-proof` one can
  show that `(b⊖a) ⋁ (bᵖ ∧ a) = ((b⊖a) ⋁ bᵖ) ∧ ((b⊖a) ⋁ a)`").
- **177V** `Theses/B/Eff/EffectAlgebras.lean:993`
  (`projections_orthomodularLattice`) — projections of a von Neumann algebra
  form an orthomodular lattice; eff.tex:559 states it as an example with no
  proof, and Mathlib has no projection lattice for W*-algebras yet.
- **178III.1** `Theses/B/Eff/EffectAlgebras.lean:1175`
  (`unitInterval_effectMonoid_unique`) — "the usual product is the only effect
  monoid structure on `[0,1]`"; eff.tex:636 asserts it without proof.
- **178III.2/.4** `Theses/B/Eff/EffectAlgebras.lean:1181`, `:1186`, `:1192` —
  every finite effect monoid is Boolean (hence commutative), and there is a
  non-commutative one on lexicographic `ℝ⁵`; eff.tex:640/651 cites these to the
  literature.
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
