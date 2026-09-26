# Adversarial review: REC 104 refutation and REC 102/103 (Reconstruction.lean)

Reviewer: independent break-it pass, 2026-09-26.  No compile needed. Every step
below was checked against short.tex and the Lean source.

## Claim 1: REC 104 false (`rec104_false`, `idem_scalar_trivial`): STANDS

Definitions against the print:
* State = **total** map I -> A: short.tex:436 ("a state is a total map I -> A";
  the substate line is commented out at :437).  Lean `Stat` =
  `{ω : effObj C ⟶ X // IsTotal ω}` (Theses/B/Eff/StatesPredicates.lean:633),
  and `IsTotal f := f ≫ truth = truth` (Theses/B/Eff/Effectus.lean:233).  Match.
* Separated by states: short.tex:457.  Lean `SeparatingStates`
  (StatesPredicates.lean:645) quantifies over all X, Y and all states of X.  Match.
  An object with no states therefore has `id = 0`.  That is correct under the
  print's definition: the condition is vacuous over an empty set of states.
* Comprehension: short.tex:~590 (`truth∘π = p∘π`, final).  Lean `IsComprehension`
  (Theses/B/Eff/Quotients.lean:497).  Match.  Totality of π (`compr_total`,
  Quotients.lean:895) needs quotients, and those come from filters.  A sequential
  effectus has filters (short.tex:1849, item 1; Lean `hasFilters` plus
  `instHasQuotients`, Reconstruction.lean:396).
* Sequential effectus: the `SequentialEffectus` class (Reconstruction.lean:285)
  matches Def 100 (short.tex:1846-1859) item by item: normal, separated by
  states, filters and comprehensions, comprehension images, dagger on pure
  maps, ⋄-adjointness in relational form, unique †-positive assert,
  `p&q = q∘asrt_p` normal SEA.
* Proof (Reconstruction.lean:1998-2023).  A state σ of {I|s} gives π∘σ = 1,
  because π∘σ is a total scalar and the only total scalar is 1.  Then
  s = s∘π∘σ = 1∘π∘σ = 1.  So for s ≠ 1 the object {I|s} has no states.  Hence
  id = 0, π = 0, and since s = s∘s factors through π_s, s = 0.  Only
  comprehension, totality of π and state separation are used; the argument is
  sound.

Informal counter-attempt.  Take C = C1 × C2, two effectuses with [0,1]
scalars, so Pred(I) = [0,1]^2 = [0,1]_{C(2 points)}.  The object (A, 0) needs a
state (ω1, ω2) with ω2 : I2 -> 0 total, so 1_{I2} = 0, which is impossible.  So
(A, 0) has no states, and separation forces A = 0.  But (A, 0) is the
comprehension of s = (1, 0).  The construction fails exactly as the Lean proof
predicts.  The remark's own justification (short.tex:1878: "on I we only need
id") checks I only and overlooks the objects {I|s}.  I found no divergent Lean
definition.

Readings under which REC 104 would be TRUE: only if "separated by states" meant
**substates** (all maps I -> A).  Then {I|s} has the substate that factors s,
the argument breaks, and product effectuses seem to satisfy it.  Nothing in the
print supports this reading (Def 14 plus :436 say total).  Suggestion (optional):
the ERRATA entry could note that the remark would hold under substate separation.
This is a possible repair, not a defect.

`rec104_false` (Reconstruction.lean:3459) is stated with T2 plus extremally
disconnected and no compactness.  That is stronger than needed and fine.  The
ERRATA's consequences all follow from `idem_scalar_trivial`, as does the
observation that the print's own Prop `predsep-splits` (short.tex:1644) is
vacuous in the state-separated case.

## Claim 2: 102/103 "as printed under three named hypotheses": STANDS, with caveats

### (b1) `AlfsenShultzResolventCriterion` (:2304): faithful and true
Hypothesis: on a Banach OUS (closed cone via `IsOUS`), a bounded δ with
`y ∉ W+ ⇒ y ∓ λδy ∉ W+` for small λ > 0 is an order derivation.  The condition
says (1 ∓ λδ)^{-1} is positive (invertible for λ‖δ‖ < 1).  Then
e^{±tδ} = lim (1 ∓ (t/n)δ)^{-n} is positive because the cone is closed, and the
two are mutually inverse, so each is an order isomorphism.  This is a true
standard fact.  It is neither vacuous nor close to the conclusion of 102/103.

### (b2) `AlfsenShultzJordanFromDerivations` (:2322): UNCLEAR (the weakest link)
It is **not** a literal statement of A–S *Geometry* 9.48/9.43.  It drops A–S's
standing setting (A and V in spectral duality, the family being the
P-projections) and replaces it by: a Banach, directed-complete OUS; an
arbitrary complement-closed family of compressions whose unit span is norm
dense; each U_i − U_{c i} an order derivation.  From this it concludes a JB
product with e_i∘w = ½(w + U_i w − U_{ci} w) for **every** i at once.

I could not build a counterexample.  I checked a 2-dim toy and a square state
space: compressions fail to exist there.  I checked that the compression axioms
make c involutive and give ker+ U_i = im+ U_{ci} both ways.  Two points remain
unverified:
* the linear extension p ↦ p∘w must be well defined on span{e_i}.  A–S get this
  from the spectral theorem and "one compression per projective unit"; here
  that must come from density and the compression axioms alone;
* no citation shows that the A–S proof survives without spectral duality.

The hypothesis is consistent: any JBW-algebra with all its projections
satisfies it.  It does not trivially imply 102/103.  But fidelity to the
literature is asserted, not shown.  Recommendation: record it as "a
reformulation of A–S 9.48 whose equivalence is unchecked", or derive it from a
literal statement.

### (b3) `WeteringStateOrderLemma` (:2516): faithful to the PRINT, but it is not a literature result
This is REC 119 itself (short.tex:2164), stated per C.  It is not van de
Wetering 2018 Prop 46.  That paper is about finite-dimensional compressible
quadratic SEAs and their SEA-states, and the print only says "exactly as".  So
`rec102`/`rec103` hold for sequential effectuses **that satisfy the print's own
Lemma 119**.  This is a gap in the print, not an external black box.  It is not
vacuous: Boolean-scalar effectuses satisfy it trivially, and vN^op satisfies it
by Cauchy–Schwarz (ω(a) = 0 ⇒ ω(pap − p⊥ap⊥) = ω(pa + ap − a) = 0).  The
docstring at :2508-2514 is honest.  The ERRATA sentence "Theorems 102 and 103
remain true" (papers/ERRATA.md:277) overclaims: Lean proves them only modulo
(b2) and (b3).  Suggest "remain true modulo the named hypotheses".

### Satisfiability of `SequentialEffectus` itself
The class has no instance anywhere in the repo (grep: none outside
Reconstruction.lean).  If it were satisfiable only trivially, 102/103 would be
hollow.  Standard models (vN^op, Pfn/Kl(D) with the classical assert) should
satisfy it, so this is not evidence of a defect.  It is untested, though.

## Claim 3 (c): Lean statements of rec102/rec103 vs short.tex:1869-1875: STANDS
* rec102 (:3418): C ≌ C1 × C2 (the parts of `dcSplitting`).  The predicates of
  C1 are CBAs (`CBAOn`, where the lattice order is ≼).  The predicates of C2 are
  order- and ⊕-isomorphic to [0,1] of a directed-complete `JBAlgebra`, and
  `JBAlgebra` (Algebras.lean:263) keeps the given OUS order and is the
  Alfsen–Shultz OUS characterisation, so it is not a free-floating product.
  The functors go to CBAᵒᵖ (monotone maps, as printed) and JB_npcᵒᵖ.  "Faithful
  iff separated by predicates" is rendered as (both faithful) ↔ SepPred, which
  is the natural reading.  JB_npc is undefined in the print (PLAN flag 11), so
  that is cosmetic.
* rec103 (:3768): either every Pred(A) is a CBA, or every one is [0,1] of a
  `JBWAlgebra` (directed complete plus separating normal states); functor
  faithful ⇔ SepPred.  Reading "CBA of JBW" as "or" is right.
* `rec102_trivial_factor` (:3448) follows correctly from Claim 1.

## Verdicts
1. REC 104 false: **STANDS**.  Print definitions match; the argument is sound;
   the only rescue is a substate reading the print does not support.
2. 102/103 under the named hypotheses: **STANDS as a Lean fact**.  Two caveats:
   (b2) is a non-literal A–S variant whose truth is unverified (UNCLEAR), and
   (b3) is the print's own Lemma 119, not an external result.  Soften the ERRATA
   wording "remain true".
3. Statement fidelity of rec102/rec103: **STANDS** (cosmetic flag 11 only).
