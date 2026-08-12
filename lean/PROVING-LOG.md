# Proving log

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
   `../berr.tex`.  **Thesis A has no `aerr.tex`**: its 27 errata/addenda live at
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

- **38VI.2** `Theses/A/CStar/TowardsVN.lean` — the "if" direction appears false
  as written: vector functionals are phase-invariant, so the constant net
  `i • x` (`x ≠ 0`) induces the same vector functional as `x` without
  converging to it.  Stated verbatim in Lean with a doc-comment flag; confirm
  against `berr.tex` when proving reaches it.
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

**The fix is `ThesisPos`, and it is cheaper than it looks.**  Define
`private def ThesisPos a := ∃ t : ℝ, ‖a − algebraMap ℂ 𝒜 t‖ ≤ t` and prove the
spine in those terms alongside the shipped statements — no restatement, so no
statement change.  17V *already contains it* as items 1–2 and now proves
`1↔2↔3` elementarily.  Estimated 400–600 lines, of which the only real work is
**`ThesisPos (a*a)` by the thesis's parsec-190 argument (~150 lines)**;
`prod_spec` (19Ia) is already proved.  The `SqrtAux` block consumes only six
lemmas, so once those exist in `ThesisPos` form the entire square-root
development transfers mechanically — and 25I becomes a genuine theorem that
*derives* the bridge instead of importing it.

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
  Parked.
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
