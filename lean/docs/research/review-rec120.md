# Adversarial review: REC 120 (`prop:assert-is-derivation`) and Theorems 102/103

Source: `papers/2109.10707/short.tex` l. 2168–2218 (REC 120), 2248–2270 (proofs of
102/103), 1846–1860 (sequential effectus), 1291–1305 (`lem:assert-image`).
Trigger: PLAN §4 flag 4, which says the step `ω' := asrt_p ∘ ω` cannot be normalised
for `C(X)`-valued scalars and that the proof uses strict inequalities in `C(X)`.

## Verdict

**102 is TRUE with a local repair of REC 120's proof.** The repair is the same for
irreducible and non-irreducible scalars. It depends on REC 119 and 121 exactly as far
as the printed proof already did, and on nothing new. The flag names a real defect in
the printing but misplaces the risk:

* 120 never needs normalisation. What it needs is a *total* state whose image lies
  under `p`, followed by one point evaluation `C(X) → ℝ`.
* The printed step is flawed for **103 as well**. `asrt_p ∘ ω` is a substate even for
  `[0,1]` scalars, and Lemma 119 (`lem:state-order-lemma`) is stated only for states.
  So 103 is no safer than 102 at this point.

## (a) The repair

Setting (as printed): `C` has convex scalars `Pred(I) ≅ [0,1]_{C(X)}` with `X` Stonean.
If `X = ∅` then `C` is trivial. `V_A` is the order unit space with
`Pred(A) ≅ [0,1]_{V_A}`, and `p&(–)` and `δ = D_p` are the linear extensions to `V_A`.
Take `y ∉ V_A⁺`, `α = ‖y⁻‖ > 0`, `x = y⁺`, and a sharp `q ≠ 0` from the spectral
theorem with `q&y ≤ -(α/2)q` and `q&x = 0`. This `q` is the paper's second `p`,
renamed. The paper's proof continues as follows, repaired:

1. **A total state under `q`.** Let `π_q : {A|q} → A` be the comprehension. The
   predicates `1` and `0` on `{A|q}` differ, since otherwise `im π_q = 0 ≠ q`. Separation
   by states then gives a state `σ : I → {A|q}`. Put `ω := π_q ∘ σ`. This is a
   **state** (total), and `im ω ≤ im π_q = q`. By `lem:assert-image`(a),
   `asrt_q ∘ ω = ω`.
   This replaces "we may assume im ω ≤ p, otherwise take ω' := asrt_p∘ω". It is the
   intended meaning of that sentence and involves no substate.
2. **Global identities in `C(X)`.** From `ω = asrt_q ∘ ω`, as elements of `C(X)`:
   * `ω(y) = ω(q&y) ≤ -(α/2)·ω(q) = -(α/2)·1`;
   * `ω(x) = ω(q&x) = 0`.
3. **Lemma 119 applied as printed**, to a genuine state with `ω(x) = 0` in `C(X)`:
   it gives `ω(δx) = 0` in `C(X)`.
4. **Evaluate at a point.** Fix any `t ∈ X` and put `φ := ev_t ∘ ω : V_A → ℝ`. The map
   `φ` is positive, linear and unital, so it is a real state, with `|φ(z)| ≤ ‖z‖` in the
   order-unit norm. Then
   `φ((1-λδ)y) = φ(y) - λφ(δ(y-x)) - λφ(δx) ≤ -α/2 + λ‖δ‖α < 0` whenever
   `λ < ½‖δ‖⁻¹`.
   So `(1-λδ)y ∉ V_A⁺`, which is the input to Alfsen–Shultz (1.82).

What this removes:
* the ill-typed paragraph "`σ(y-y') < (α/2)σ(1)` … `‖ω‖ ≤ -(2/α)ω(y)`" (now `‖φ‖ = 1`);
* all strict inequalities in `C(X)` (they now live in `ℝ`), and any division by `ω(q)`.

Typos: `λ < ½‖δ‖` should read `λ < ½‖δ‖⁻¹` (l. 2183); `p` is reused for the idempotent.

The same repaired proof serves 103: with `X = {pt}`, `ev_t` is the identity.

## (b) Counterexample attempts (all fail)

* **Direct sums with different scalars.** Take `C = C' × C''` with scalars
  `{0,1} × [0,1]` or `[0,1] × [0,1] = [0,1]_{C(2)}`. The splitting
  (`prop:splits-directed-complete`) removes the Boolean factor. On the convex factor,
  `V_{(A,B)} = V_A ⊕ V_B`, the `D_p` act componentwise, and the repaired step 4 picks a
  point `t` in the component where `q ≠ 0`. No failure.
* **Connected `X`.** Excluded by the hypotheses. A sequential effectus is normal
  (directed-complete), so `Pred(I)` is a dc effect monoid ≅ `B ⊕ C(X,[0,1])` with `X`
  Stonean (REC 34 / OAP 69). A connected Stonean space is a point. `C([0,1])`-valued
  scalars are therefore not a legal test case, and irreducible scalars
  (`{0},{0,1},[0,1]`) are exactly the case of a one-point `X`.
* **Bundle / stalk reduction over `X`** (102 to 103): not needed, not available. Points
  of a non-discrete Stonean `X` are not clopen, `prop:predsep-splits` splits only along
  clopens, and an ultrafilter stalk loses directed completeness. By l. 1878, `V_I = C(X)`
  need not be JBW, so 102 genuinely differs from 103 and cannot be reduced to it.

## (c) What 102 correctly states

This is as printed, with cosmetic fixes (PLAN flag 11). `C ≃ C₁ × C₂`, where:
* every `Pred(A)` in `C₁` is a complete Boolean algebra;
* every `Pred(A)` in `C₂` is the **unit interval** of a directed-complete (monotone
  complete) JB-algebra `V_A`;
* `Pred : C₁ → CBAᵒᵖ` and `C₂ → JB_{npc}ᵒᵖ`, with `JB_{npc}` defined analogously to
  `JBW_{npc}` (normal positive contractive/unital maps between dc JB-algebras), are
  faithful iff `C` is separated by predicates.

No strengthening to JBW is available (see above). No weakening is needed because of 120.

## Residual risks for 102 (not caused by 120, but load-bearing)

1. **REC 119 for `C(X)`-valued states.** The printed "proof" is a citation ("exactly
   as" van de Wetering 2018, Prop 46). It must be re-derived for `C(X)`-valued internal
   states. The repair uses it only in its printed form (a total state, vanishing
   globally in `C(X)`), so there are no pointwise hypotheses. One possible in-house
   route: `x∘ω = 0` ⇒ `im ω ≤ ⌈x⌉^⊥ =: r` ⇒ `ω = asrt_r ∘ ω`. It then suffices that
   `ξ^{r^⊥} ∘ asrt_q ∘ π_r = ξ^{r^⊥} ∘ asrt_{q^⊥} ∘ π_r`, which in `B(H)` is
   `r^⊥qr = -r^⊥q^⊥r`. This identity is where "quadratic" (`cor:assert-is-quadratic`)
   must do the work. I have not verified it from the axioms. If Prop 46's argument
   divides by `ω(…)` or uses real-valuedness, *this* is where the 102-vs-103 gap would
   reappear. Recommend an adversarial check of 119 on its own.
2. **REC 121 (A–S Geometry 9.48/9.43).** Check that the cited theorem does not assume
   spectral duality (`A = V*`, normal states separating), because `V_A` need not be a
   dual space in the `C(X)` case. The sketch uses only `D_p`, A–S *State spaces* 1.114
   (general Banach OUS), density of sharp combinations and norm continuity, so it is
   likely fine; but `AlfsenShultzJordanFromDerivations` must be *stated* for Banach OUS
   with a norm-dense spectral family, not JBW-type duals, or 102 inherits an
   unprovable hypothesis.
3. `V_A` must be a **Banach** OUS for (1.82). It comes from `DCOUS ≃ DCEA_c` plus Wright
   (PLAN, row 42), and is already accounted for.

## Should PLAN reorder to do 103 first?

**No.** 103's proof invokes 102's pipeline ("the previous results give
`Pred : C → JB_npcᵒᵖ`") and adds only the JBW step; the repaired 120 is one proof for
both. Reordering helps only if 119 turns out to need real-valued states: then 103
(`X = pt`) is the fallback, and 102 becomes GAP at 119, not at 120.

PLAN edits: in flag 4, replace "for irreducible scalars the argument reads correctly"
with "also wrong for `[0,1]` scalars (a substate is fed to a lemma about states);
repaired uniformly by `ω := π_q ∘ σ` plus evaluation at a point of `X`". Mark 119 (for
`C(X)`-valued states) and the hypotheses of the 121 black box as the real risks for 102.
Filing: file 120 as "proof under-specified (substate, ill-typed `C(X)` inequalities);
statement true, local repair". A reader stumbles at "take `ω' := asrt_p∘ω`".
