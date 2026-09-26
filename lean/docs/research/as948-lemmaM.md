# Lemma M (the Peirce-½ half of the REC 121 symmetry) — a proof attempt

Research note, 2026-09-26.  No Lean edits.  Inputs: as948-discharge.md (with its
Review), as948-reformulation.md, short.tex:2150-2237 (REC 118-121), :978-1070
(SEA axioms, normal-SEA facts), Reconstruction.lean:2276-2336 (`IsOrderDerivation`,
the two A–S named Props), :2520 (`WeteringStateOrderLemma`).  Numerics: numpy in
M_4 (scratch `lemM-check.py`), sanity only.  **Every result below is claimed**, for
adversarial review.  A–S numbering is from memory: [unverified] where marked.

Notation as in as948-discharge: U_r := asrt_r on V_A, D_r := U_r − U_{r⊥},
T_r := ½(1 + D_r), x := T_p q − T_q p for sharp p, q.  Known (reviewed):
[D_p, D_q]1 = 4x.  Lemma M: x = 0.

## 0. Verdict: (a) — M follows from REC 120 plus A–S *State spaces* 1.114

The whole symmetry (corners *and* Peirce-½ part) follows from the hypotheses the
abstract Lean Prop already carries, plus one textbook fact the print itself cites
at the very step (short.tex:2233): the commutator of two order derivations is an
order derivation.  No states, internal or real, are needed, and no spectral
duality.  The key observation the earlier note missed: **x lies in ker D_p ∩ ker D_q**,
so δ := [D_p, D_q] satisfies δ1 = 4x and δ²1 = 4δx = 0, and e^{tδ}1 = 1 + 4tx
*exactly*, for every t ∈ ℝ.  Positivity of e^{tδ} for t → ±∞ then forces x = 0.

## 1. Lemma P (order-derivation kernel principle; claimed)

Let W be an Archimedean order unit space, δ : W → W bounded with e^{tδ} ≥ 0 for all
t (e^{tδ} := norm limit of the partial sums, as in `IsOrderDerivation`), Φ : W → W
positive linear, a ≥ 0 with Φa = 0.  Then Φ(δa) = 0.

Proof.  Φ is order-unit-norm bounded (−‖v‖1 ≤ v ≤ ‖v‖1 gives ±Φv ≤ ‖v‖Φ1), so
Φ(e^{tδ}a) = Σ_n tⁿΦ(δⁿa)/n! = tΦ(δa) + t²ρ(t) with ‖ρ(t)‖ ≤ K := ‖Φ‖‖δ‖²‖a‖e^{‖δ‖}
for |t| ≤ 1.  Positivity gives, for 0 < t ≤ 1, tΦ(δa) + t²ρ(t) ≥ 0, so
Φ(δa) ≥ −tK·1; Archimedean ⇒ Φ(δa) ≥ 0.  For −1 ≤ t < 0 the same gives
Φ(δa) ≤ 0.  ∎  (This is the "only if" half of A–S 1.108 [unverified numbering],
with a positive map in place of a state; no state is used.)

## 2. The four corners, from Lemma P alone (claimed; replaces §2 of as948-discharge)

Facts available for sharp p (Lean Prop hypotheses / REC 100, 109): U_p, U_{p⊥}
positive, U_p1 = p, U_p² = U_p, U_pU_{p⊥} = U_{p⊥}U_p = 0; hence U_{p⊥}p = 0,
U_p p = p, U_p p⊥ = 0.  REC 120: D_q is an order derivation.

* Lemma A':  U_{p⊥}D_q p = 0.  (Lemma P with Φ = U_{p⊥}, a = p, δ = D_q.)
* Lemma B':  U_p D_q p⊥ = 0, hence U_p D_q p = U_p D_q 1 = U_p(2q − 1) = 2U_p q − p.
  (Lemma P with Φ = U_p, a = p⊥ = 1 − p ≥ 0.)

A' is the discharge note's Lemma A (U_{p⊥}U_q p = U_{p⊥}U_{q⊥}p) and B' is its
Lemma B, now without REC 119, states, comprehensions or the substate repair.

Corners.  Write 2x = (q + U_p q − U_{p⊥}q) − (p + U_q p − U_{q⊥}p).
* 2U_{p⊥}x = (U_{p⊥}q + 0 − U_{p⊥}q) − (0 + U_{p⊥}D_q p) = 0 by A'.
* 2U_p x = (U_p q + U_p q − 0) − (p + U_p D_q p) = 2U_p q − p − (2U_p q − p) = 0 by B'.
* p ↔ q sends x ↦ −x, so U_q x = U_{q⊥}x = 0.
Hence **D_p x = 0 and D_q x = 0.**  Numerics (M_4): A', B' residuals 2e-16.

## 3. Lemma M (claimed)

Let δ := [D_p, D_q] = D_pD_q − D_qD_p.
1. δ1 = 4x (reviewed claim 1 of as948-discharge).
2. δx = D_p(D_q x) − D_q(D_p x) = 0 by §2.  So δⁿ1 = 0 for n ≥ 2.
3. **δ is an order derivation**: A–S *State spaces* Prop. 1.114 [unverified
   numbering; the print cites exactly this at short.tex:2233].  Self-contained
   proof for bounded X, Y on a Banach space with closed cone: with
   Z_s := e^{sX}e^{sY}e^{−sX}e^{−sY} = 1 + s²[X,Y] + s³R(s), ‖R(s)‖ ≤ K for |s| ≤ 1,
   one has Z_s^n → e^{t[X,Y]} for s = √(t/n), t > 0 (telescoping:
   ‖Z_s^n − e^{tC}‖ ≤ n‖Z_s − e^{s²C}‖·max(‖Z_s‖,‖e^{s²C}‖)^{n−1} = n·O(n^{−3/2})·O(1),
   the last factor bounded because ‖Z_s‖ ≤ e^{s²‖C‖ + |s|³K}).  Each Z_s is a
   composite of positive maps (e^{±sX}, e^{±sY} ≥ 0 since X, Y are order
   derivations), positive maps are closed under norm limits (closed cone), so
   e^{tδ} ≥ 0; t < 0 is the same with X, Y swapped; e^{tδ}e^{−tδ} = 1 makes each an
   order isomorphism.  Only the Banach OUS structure is used — no predual, no
   spectral duality, no states.
4. By 1–2 the partial sums of e^{tδ}1 are 1 + 4tx from N = 1 on, so e^{tδ}1 = 1 + 4tx.
5. e^{tδ} is an order isomorphism, so 1 + 4tx = e^{tδ}1 ≥ e^{tδ}0 = 0 for all t ∈ ℝ.
   For t > 0: x ≥ −(4t)⁻¹·1 for all t; Archimedean ⇒ x ≥ 0.  For t < 0: x ≤ 0.
   So **x = 0**, i.e. T_p q = T_q p, i.e. [D_p, D_q]1 = 0.  ∎

Equivalent state form (the brief's hint, as a cross-check; claimed).  Take a real
state ω of the Banach OUS V_A with ω(x) = ‖x‖ (exists by Hahn–Banach/compactness
after replacing x by −x if needed; it is "supported on ⌈x⁺⌉", off every corner).
Put a := ‖x‖·1 − x ≥ 0, so ω(a) = 0.  Lemma P with Φ = ω, δ as above:
0 = ω(δa) = ‖x‖ω(δ1) − ω(δx) = 4‖x‖ω(x) = 4‖x‖².  Same content; the exponential
form in step 5 avoids needing a norm-attaining state.

Why the earlier note missed it: it applied the order-derivation condition for δ
only to a ∈ {p, p⊥, q, q⊥} and corner states, where it re-derives A', B'.  The
element that matters is a = ‖x‖1 − x (or, equivalently, the exact exponential),
and the fact that makes it work is δx = 0, which is the corner lemmas themselves.

## 4. What this uses, and does not use

Used: U_r positive idempotent with U_r1 = r, U_rU_{r⊥} = 0 (r ∈ {p, p⊥, q, q⊥});
D_p, D_q order derivations (REC 120, in Lean `rec120` under
`AlfsenShultzResolventCriterion` + `WeteringStateOrderLemma`); A–S 1.114
(commutator of order derivations); V_A Archimedean, Banach (`IsOUS`, `IsBanachOUS`).
Not used: REC 119 directly, internal states, separation by states, comprehensions,
the SEA axioms beyond p⊥ & p = 0 and p & p = p, spectral theorem, density,
A–S 9.48, any predual.  In particular the argument goes through verbatim for the
**abstract Prop** `AlfsenShultzJordanFromDerivations`: with δ_ij := [D_i, D_j],
its hypotheses give T_i e_j = T_j e_i for all i, j once 1.114 is available.

Not a general fact: "[X,Y]1 = 0 for all order derivations X, Y" is **false**
(X = L_b, Y a Jordan derivation d in a JB-algebra: [X,Y] = −L_{db}, [X,Y]1 = −db).
The proof needs δx = 0, i.e. x ∈ ker D_p ∩ ker D_q, which is special to x.  (I
also checked that a second-order expansion e^{tX}e^{sY}e^{−tX}e^{−sY}1 =
1 + ts[X,Y]1 + O(3) ≥ 0 gives nothing: the leading 1 dominates for small s, t.
Only the exact identity for all t works.)

## 5. Consequences (for the caller; no edits made)

* **Lean.**  Introduce a named hypothesis `AlfsenShultzCommutatorOfOrderDerivations`
  (A–S *State spaces* 1.114: on a Banach OUS, bounded order derivations are closed
  under commutator) — or prove it via §3.3 (real analysis on their `expPartialSum`,
  several hundred lines; the named hypothesis is the honest cheap option and the
  print cites it).  Then H1 (symmetry) is a *theorem* from the Prop's hypotheses:
  Lemma P (~50 lines), corners (~60), exact exponential + Archimedean (~40).
  `AlfsenShultzJordanFromDerivations` shrinks to H2, the 9.43 transplant
  (well-definedness on the span from H1 per as948-reformulation §3b ~100 lines;
  continuity, Jordan identity, 0 ≤ a² ≤ 1 stay named).  Trust base:
  {h119, ResolventCriterion, 1.114, H2} instead of {h119, ResolventCriterion, H1+H2}.
* **ERRATA REC 121 (commit 1bffa67).**  Its sentence "the Peirce-½ component is not
  derived" should become, if this note survives review: "the symmetry
  [D_p,D_q]1 = 0 follows from Prop. 120 and A–S *State spaces* 1.114 by a short
  argument (research note as948-lemmaM); what the citation of 9.48 leaves
  unargued in this setting is the remainder of 9.43 (continuity, Jordan identity,
  0 ≤ a² ≤ 1)".  The out-of-hypotheses citation of 9.48 still stands as filed.
* **as948-discharge §2** can be simplified: Lemmas A, B need no states (Lemma P),
  so the Review's substate repair becomes unnecessary (though still correct).

## Claimed, for adversarial review
1. Lemma P and its tail estimate; Archimedean closing step.
2. A', B' from Lemma P with the listed U-identities; the corner algebra; D_p x = D_q x = 0.
3. δx = 0 ⇒ e^{tδ}1 = 1 + 4tx for all t, under Lean's `IsOrderDerivation` (limit of
   partial sums; e an order isomorphism).
4. A–S 1.114 holds for bounded order derivations on any Banach OUS (group-commutator
   formula sketch in §3.3; numbering unverified; print cites it at :2233).
5. The state-form cross-check (norm-attaining state exists; ω(δa) = 4‖x‖²).
6. The consequences in §5, in particular that the abstract Prop's hypotheses suffice.

## Review (2026-09-26)

Adversarial review against Reconstruction.lean:2262-2336 (`expPartialSum`,
`IsOrderDerivation`, the A–S Props), Algebras.lean:180-195 (`ousNorm`, `IsOUS`,
`IsBanachOUS`), `rec120` (:2740), short.tex:2227-2237.  No numerics needed: every
step is finite algebra or a standard estimate, checked by hand.  **Verdict: the
proof stands.**  No break found.

1. **Lemma P — STANDS.**  `IsOrderDerivation` gives, per t, a linear order
   isomorphism e_t with e_t v the norm limit of `expPartialSum`; so e_t ≥ 0.
   Archimedean is not a separate field but follows from `IsOUS.cone_closed`
   (if v + ε1 ≥ 0 ∀ε, then ‖v − (v+ε1)‖ ≤ ε).  Φ positive ⇒ ‖Φv‖ ≤ ‖Φ1‖‖v‖
   (with λ > ‖v‖ if the inf in `ousNorm` is not attained), so Φ commutes with
   the limit; the tail e_t a − a − tδa exists (difference of limits) with norm
   ≤ t²c²‖a‖e^c for |t| ≤ 1; and ρ ≤ K·1 gives tΦ(δa) ≥ −t²K·1 — sign checked.
   Φa = 0 kills the constant term.  Correct as stated for any positive Φ (W→W or W→ℝ).
2. **A', B', corners, D_p x = D_q x = 0 — STANDS.**  c is an involution
   (e(c(c i)) = e i, e injective), so U_{p⊥}U_p = 0 as well as U_pU_{p⊥} = 0;
   hence U_{p⊥}p = 0 and U_p p⊥ = p − U_pU_p1 = 0.  δ = D_q is an order
   derivation (Prop hypothesis / `rec120`).  D_q1 = 2q − 1.  Recomputed
   2U_{p⊥}x = 0 and 2U_px = 2U_pq − (p + 2U_pq − p) = 0 term by term; p ↔ q
   gives x ↦ −x.  Since D_r = U_r − U_{r⊥} by definition (`Dop`, and the Prop's
   `U i - U (c i)`), D_px = D_qx = 0.  (Lemma P is exactly A–S 1.108 "only if"
   with a positive map; it makes the states/substate repair of as948-discharge §2
   unnecessary.)
3. **δ1 = 4x, δx = 0, e^{tδ}1 = 1 + 4tx — STANDS.**  δ1 = D_p(2q−1) − D_q(2p−1)
   = 2D_pq − (2p−1) − 2D_qp + (2q−1) = 2(q + D_pq) − 2(p + D_qp) = 4x.
   δx = D_pD_qx − D_qD_px = 0, so partial sums are 1 + 4tx from N = 2 on.
4. **Commutator of order derivations — STANDS** (numbering of A–S 1.114 still
   unverified; the print cites "Prop. 1.114" for exactly this).  Lean's e_t
   coincides with the operator-norm exponential (B(W) Banach as W is; limits
   unique as `ousNorm` is a norm).  Z_s = 1 + s²C + O(s³); telescoping bound
   n·O(n^{−3/2})·e^{t‖C‖+o(1)} → 0; each Z_s^n positive; limit positive by
   `cone_closed`; t < 0 via [X,Y] = −[Y,X]; e^{tδ}e^{−tδ} = 1 ⇒ order
   isomorphism; δ bounded.  This is the Lie–Trotter commutator formula; it
   needs only `IsOUS` + `IsBanachOUS`, so it is *provable* in Lean, not merely
   nameable.  Only positivity (not the full order-iso) of e^{tδ} is used in step 5.
5. **x = 0 — STANDS.**  1 + 4tx ≥ 0 ∀t; t → ±∞ with `cone_closed` gives x ≥ 0
   and x ≤ 0.  State cross-check also correct (norm-attaining state on an OUS
   exists; 0 = ω(δ(‖x‖1 − x)) = 4‖x‖²), but not needed.
6. **Consequences — STANDS, with one precision.**  The abstract Prop's
   hypotheses (U_i positive, U_i1 = e_i, U_i² = U_i, U_iU_{ci} = 0, each
   U_i − U_{ci} an order derivation, `IsOUS`, `IsBanachOUS`) plus the commutator
   fact yield T_ie_j = T_je_i for all i, j; neither density, directed
   completeness nor the kernel condition is used.  In REC's setting the only
   inputs are `rec120` (hence `AlfsenShultzResolventCriterion` +
   `WeteringStateOrderLemma`, already carried) and the commutator fact.  What
   remains genuinely named: the 9.43 transplant (continuity of a ↦ T_a on the
   span, Jordan identity, −1 ≤ a ≤ 1 ⇒ 0 ≤ a² ≤ 1); well-definedness on the
   span needs the symmetry (now proved) per as948-reformulation §3b.
   Recommend proving the commutator lemma rather than naming it (it is ordinary
   analysis; if named, name it by content, not by the unverified number).

**ERRATA REC 121.**  The print's own ingredients — Prop. 120 and the commutator
fact it cites at :2233 — do suffice for [D_p,D_q]1 = 0; what the print lacks is
the "some algebra" (the corner lemmas giving δx = 0, then e^{tδ}1 = 1 + 4tx), which
it attributes to 9.48, a theorem whose hypotheses (spectral duality) are not
established.  Proposed replacement of the entry's middle sentences:
"…which the paper does not establish for V_A.  The step is repairable from the
paper's own ingredients: Prop. 120 and the commutator fact it cites give
[D_p, D_q]1 = 0 by a short argument not in 9.48 (x := T_pq − T_qp is killed by
D_p and D_q, so e^{t[D_p,D_q]}1 = 1 + 4tx for all t, and positivity forces
x = 0; research note as948-lemmaM).  The remaining parts of the proof, transplanted
from 9.43 (continuity, Jordan identity, 0 ≤ a² ≤ 1), are sketched only and not
checked here.  The statement is not refuted."  Whether the corrected entry still
meets the "a reader would stumble" bar is the author's call: the citation of 9.48
outside its hypotheses and the missing argument remain real, but the gap is now
a short fix, not an open problem.  Drop "the Peirce-½ component we could not
derive" and the REC 119/comprehensions route in any case.

**Citations verified (2026-09-26, `rec-citations.md`):** A–S *State spaces* Prop. 1.108 (p. 58) and Prop. 1.114 (p. 60, order derivations closed under Lie brackets) are the numbers used above; the "[unverified]" marks are resolved.
