# Jordan Fuglede–Putnam: the hard half of van de Wetering's theorem for general `a` (JBW)

Status: **CLAIMED, not yet adversarially reviewed.** Research note, 2026-09-26. No Lean.
Scratch checks: `scratchpad/jfp-albert.py`, `jfp-ops.py` (identities checked numerically in
the Albert algebra `H₃(𝕆)`, i.e. exceptionally, so they are genuine Jordan identities).

Notation: `x = √a`, `y = √b`, `X = L_x`, `Y = L_y`, `P = L_{x²}`, `A := x∘y`, `Q = L_A`,
`D := [X, Y]` (a derivation), `U = U_x = 2X² − P`, `u | v` = operator commute.

## 0. What van de Wetering actually does (arXiv 1912.01903, JPAA 2020)
Not portable. Prop 3.3 (JC-algebras): `ab²a = ba²b` ⇒ `ab` normal ⇒ Fuglede–Putnam–Rosenblum
⇒ `ba² = a²b`. Prop 3.7: Shirshov–Cohn for JB(W) (HOS 7.2.5/7.2.6) to make the pair special.
Prop 3.11/Thm 3.12: JBW = JW ⊕ `C(X, H₃(𝕆))` (Shultz), JW part via 3.3, exceptional part via
EJA Prop 3.9 (FP in `B(E)`, `E` Hilbert). Thm 3.13 (JB): pass to `A**`. Remark 2.15: even
"`a | b ⇒ a | b²`" is left to structure theory. None of this is in the repo.

## 1. Question (1): yes, an identity in every Jordan algebra
`[X,Y](x∘y) = ¼(U_x y² − U_y x²)`. Proof: `jb_lin` operator form `[L_a,L_{bc}] + [L_b,L_{ca}]
+ [L_c,L_{ab}] = 0` at `(x,x,y)` applied to `y`, and at `(y,y,x)` applied to `x`; subtract.
So hypothesis ⇔ `D(A) = 0` ⇔ `[D, Q] = 0` (`[D, L_w] = L_{Dw}`).

## 2. The key identity (JK) — no hypothesis needed
  **(JK)  `[Q, U] + D U + U D = 0`**, i.e. `[2Q + 2D, U] = −4 U D`.
(In `B(H)`: `2Q + 2D = ℓ_T + r_{T*}` with `T = xy`, and `xT* = Tx`; this is the Jordan shadow of
Fuglede's intertwining.) Checked numerically in `H₃(𝕆)` (error 1e-13 at scale 1e3). Derivation
(all in `B(A)`): `[X,P] = 0`; `jb_lin(x,x,y)`: `[Q,X] = ½[Y,P]`; `jb_lin(x,x,A)`:
`[Q,P] = −2[X, L_{x∘A}]`; second-order linearisation (`L_{(ab)c}` formula, as in
`JBMacdonald.two_U2_mul`) at `(x,y,x)`: `L_{x∘A} = 2QX + PY − X²Y − YX²`. Then
`[Q,P] = 2[Y,P]X − 2PD + 2X²D + 2DX²`, `[Q,U] = 2[Q,X²] − [Q,P] = [X,[Y,P]] + 2PD − 2X²D −
2DX²`, and `[Q,U] + DU + UD = [X,[Y,P]] − [D,P] = 0` by Jacobi (`[X,P] = 0`).

## 3. Proof sketch (JBW-algebra; positivity of `x, y` only used at the very end)
**Step A (flow identity).** Assume `D(A) = 0`. Put `M = 2Q + 2D`; `Q, D` commute, so
`e^{σM} = e^{2σQ} e^{2σD}`, and `e^{2σQ} = U_{e^{σA}}` (`Uo_eE`). Let
`Φ(σ) = e^{σM} U e^{−σM}(1)`. `Φ' = e^{σM}[M,U]e^{−σM}(1) = −4 e^{σM} U D (e^{−2σA}) = 0`,
since `e^{−σM}1 = e^{−2σA}` (`D1 = 0`) and `D` kills `C(A)` (Leibniz + continuity).
`Φ(0) = x²`. Rearranged:
  **(K')  `U_{e^{σA}} U_x (e^{−2σA}) = e^{−2σD}(x²)`  for all real `σ`.**
(In `B(H)`: `(e^{σA}xe^{−σA})(…)* = e^{−σC/2}x²e^{σC/2}`, `C = [x,y]`.)
`e^{tD}` is a Jordan automorphism (exp of a derivation), hence positive & unital, hence
`‖e^{tD}‖ ≤ 1`: the LHS of (K') is bounded by `‖x‖²` uniformly in `σ`.

**Step B (gap ⇒ Peirce vanishing).** Fix `s`, `ε > 0`, `q = χ_{≥s+ε}(A)`, `r = χ_{≤s}(A)`
(spectral projections, `q ⊥ r`, everything in the associative `W(A)`). With `σ = −τ`, `τ > 0`:
`e^{2τA} ≥ e^{2τ(s+ε)} q`, so `V := U_{e^{−τA}} U_x(e^{2τA}) ≥ e^{2τ(s+ε)} U_{e^{−τA}}U_x q`;
compress by `U_r` and use `U_r U_{e^{−τA}} = U_c`, `c = r∘e^{−τA}`, `U_r = U_{c'}U_c` on
positives with `c' = r∘e^{τA}`, `‖c'‖ ≤ e^{τs}`, `‖U_w v‖ ≤ ‖w‖²‖v‖`, monotonicity of norm on
`0 ≤ v ≤ w`:  `‖U_r U_x q‖ ≤ e^{−2τε} ‖x‖²` for all `τ` ⇒ **`U_r U_x q = 0`**.
Let `ε ↓ 0`: `q ↑ p := χ_{>s}(A)`, `r = 1 − p`; `U_r U_x` is good (`good_Uo`, `good_mul`), so
`U_{1−p} U_x p = 0`, which is `P₀(p)`-part of `(P½(p)x)²` ⇒ `P½(p) x = 0` (`half_eq_zero`
pattern, as in `JBSeqComm` step 2) ⇒ `x | p` for every spectral projection of `A`
⇒ **`x | A`** (`opComm_of_sprojs`, adapted to the repo's `sproj (rampF …)`).
Symmetrically `y | A`.

**Step C (Jordan FP).** `jb_lin(x,x,y)`: `2[X,Q] + [Y,P] = 0`, so `x | A` ⇒ **`y | x² = a`**;
likewise `x | b`. (This is exactly FP's conclusion `x²y = yx²`; no positivity used.)

**Step D (single-element commutant, new lemma, JBW).** *If `y | a` then `y` op-commutes with
every spectral projection of `a`*; hence `y ∈ comm(C(a))`, and `b = y² ∈ comm(C(a))` by
`jbw_mul_mem`. Proof (a ≥ 0 WLOG by shifting): `q = χ_{≥s+ε}(a)`, `r = χ_{≤s}(a)`,
`a₁ = a∘q ∈ V₁(q)`, `a₀ = a∘(1−q) ∈ V₀(q)`, `z = P½(q) y`.
(i) `[L_y, L_a] q = 0`, projected on `V½(q)` with Peirce rules: `a₁∘z = a₀∘z`.
(ii) Peirce `U_{V₁}V½ = U_{V₀}V½ = 0`, linearised: for op-commuting `u, v` both in `V₁(q)` (or
both in `V₀(q)`), `(2L_u)(2L_v) = 2L_{u∘v}` on `V½(q)`. All of `a₁, a₀, r, c := (a₁)⁻¹_{V₁(q)}`
lie in `W(a)`, so their `L`'s commute.
(iii) `z' := 2L_r z`: `(2L_{a₁}) z' = (2L_{a∘r}) z'` (use (ii) with `a₀∘r = a∘r`, `r² = r`).
(iv) `z' = (2L_{cⁿ})(2L_{(a∘r)ⁿ}) z'`, `‖cⁿ‖ ≤ (s+ε)^{−n}`, `‖(a∘r)ⁿ‖ ≤ sⁿ`:
`‖z'‖ ≤ 4(s/(s+ε))ⁿ‖z'‖` ⇒ `z' = 0`, i.e. `U_{q,r} y = 0` (`2L_r P½(q) = 2U_{q,r}` for `r ⊥ q`).
(v) `q ↦ U_{q,r}y` is linear and normal (L-operators are `Nrm`), `q ↑ χ_{>s}(a)` ⇒
`P½(χ_{>s}(a)) y = 0`. (This answers van de Wetering's Remark 2.15 for JBW, trace-free.)

**Conclusion.** Hypothesis ⇒ (1) `D(A)=0` ⇒ (K') ⇒ `x | A` ⇒ `y | a` ⇒ `b ∈ comm(C(a))`:
`JBSeqComm.mem_comm` for every JBW-algebra, general `a`. The JB case needs `A ↪ A**` (not in
repo); otherwise JB is only reached for finite spectrum (existing `mem_comm_frame`).

## 4. Lean shopping list (all portable)
1. `(1)` and `(JK)` as operator identities in `B(A)` (two `jb_lin` + one second-order
   linearisation; `JBMacdonald.two_U2_mul` is the template).
2. `exp` of a bounded derivation is a Jordan automorphism, positive, `‖·‖ ≤ 1`.
3. ODE/constancy of `Φ` (template: `JBMacdonald` step 2, `hasDerivAt_Uo`, `Uo_eE`).
4. Spectral-projection inequalities in `W(A)`: `e^{2τA} ≥ e^{2τ(s+ε)}χ_{≥s+ε}(A)`,
   `‖r∘e^{τA}‖ ≤ e^{τs}`; `U_uU_v = U_{u∘v}` for `u, v ∈ W(A)`; sup of `χ_{≥s+ε}` is `χ_{>s}`.
5. Peirce: `U_{V₁}V½ = 0 = U_{V₀}V½`; `2L_r P½(q) = 2U_{q,r}` for `r ⊥ q`; `U_{1−p}U_x p = 0 ⇒
   P½(p)x = 0`.

## 5. Points for the adversarial review
- (JK) is verified numerically in `H₃(𝕆)` and in the hand derivation above; re-derive the
  `L_{x∘A}` instance of the second linearisation carefully (a sign slip was caught once).
- Step A uses `D(e^{−2σA}) = 0` and `[Q, D] = 0` — both from `D(A) = 0` only.
- Step B: check the ε-limit really yields `χ_{>s}` with `1 − χ_{>s} = χ_{≤s}` in the repo's
  `sproj (rampF …)` conventions; `A = x∘y` need not be positive (fine: shift).
- Step D (iii): `z'` lives in `V½(q)` and `2L_r` preserves it; `c` exists since `a₁ ≥ (s+ε)q`,
  `s+ε > 0` (for `s < 0`, `r = 0`).

## Review (2026-09-26)
Adversarial review, numerics only (scratch `revjfp-{hand,fast,run,stepD,chk}.py`). **Verdict: the
chain STANDS mathematically; no break found. Lean gaps below are technical, not conceptual.**

**(1), (JK): STAND.** Re-ran `jfp-albert.py`/`jfp-ops.py` (errors ~1e-13). Each hand step of §2
checked separately in `H₃(𝕆)` (random x, y): `[X,P]=0`, the `[Q,P]` formula, the `[Q,U]` formula
and the final Jacobi step all hold to 1e-13; `D` is a derivation (5e-15). Independent reason
these are genuine identities: both sides of (JK)·z are linear in `z` and in the 3 variables
`x, y, z`, so Macdonald's theorem already gives them from the special case.

**Step A: STANDS.** `[M,U] = 2[Q,U] + 2[D,U] = −4UD` ✓; `e^{−σM}1 = e^{−2σQ}1 = e^{−2σA}` ✓
(`Uo_eE`: `U_{e^h} = e^{2L_h}`); `[D,Q] = L_{DA}` ✓. (K') tested in `H₃(𝕆)` on *genuinely
non-commuting* solutions of `U_x y² = U_y x²` found by Newton (x, y not positive, `‖[L_x,L_y]‖`
up to 3.4): error 1e-15…7e-13 for σ = 0.3, −0.5. (Two positive-case runs gave large errors: those
are exp overflow at ‖A‖≈15 with D≈1e-8, not a counterexample.) `e^{tD}` is an automorphism
numerically (1e-15). Contractivity: automorphism ⇒ maps squares to squares and 1 to 1 ⇒ positive
unital ⇒ ‖·‖ ≤ 1 in the order-unit norm. Not in the repo; needed only as `‖e^{tD}‖ ≤ 1`.

**Step B: STANDS.** Re-derived: with `W = U_{e^{−τA}}U_x q ≥ 0`, `V = e^{2τD}x² ≥ e^{2τ(s+ε)}W`,
`U_rU_xq = U_{c'}W ≤ e^{−2τ(s+ε)}U_{c'}V`, `‖c'‖² ≤ e^{2τs}` ⇒ `‖U_rU_xq‖ ≤ e^{−2τε}‖x‖²` ✓. The
direction of σ is right. The repo's `sproj (rampF a δ j)` is the support of `(t+‖a‖−jδ)⁺`, i.e.
`χ_{>s}` with `s = jδ−‖a‖`, which is exactly what B and D produce, and `opComm_of_sprojs` asks
for exactly these ✓. `U_{1−p}U_xp = 0 ⇒ P½(p)x = 0` is the `JBSeqComm` step-2 pattern with
`p ↔ 1−p` ✓. Numerically, on the non-commuting `H₃(𝕆)` solutions, `‖[L_x, L_q]‖` ≤ 2e-14 for every
spectral projection `q` of `A`, and `[X,Q] = 0` to 1e-15 (so Jordan FP really holds in the
exceptional case, not only through the special case).
*Lean gap:* `U_rU_{e^{τA}} = U_{r∘e^{τA}}` with `r` a **spectral projection** (in `W(A)`, not
`C(A)`). Macdonald covers polynomials/continuous functions of `A`; passing to `r` needs
σ-weak continuity of `u ↦ U_u` along monotone nets in `W(A)` (the product is only separately
normal), or a restatement with continuous cut-offs `f(A), g(A)` and the limit taken only at the
end. Add this to §4 item 4.

**Step C: STANDS.** `2[X,Q] + [Y,P] = 0` (H₃(𝕆), 2e-14); in `B(H)` it is the usual
`x(xy+yx) = (xy+yx)x ⇔ x²y = yx²`. Needs no positivity. Numerically also `[L_x, L_{y²}] = 0` on the solutions.

**Step D: STANDS.** Checked by hand: (i) the `V½(q)` component of `[L_y,L_a]q = 0` is
`a₁∘z = a₀∘z` ✓; (ii) `{V₁V½V₁} ⊂ V_{3/2} = 0`, `{V₀V½V₀} ⊂ V_{−½} = 0` ⇒
`(2L_u)(2L_v) = 2L_{u∘v}` on `V½` for op-commuting `u, v` ✓; (iii) uses `[L_r, L_{a₁}] = 0` ✓;
(iv) the iterate `(2L_{a₁})ⁿz' = (2L_{a∘r})ⁿz'` needs induction with `[L_{a₁},L_{a∘r}] = 0` (not
only (iii) once) ✓; bound `4(s/(s+ε))ⁿ` ✓; `c = χ_{≥s+ε}(t)/t (a)` exists ✓. (v)
`U_{p,1−p} = ½P½(p)` ✓, linear in `q` ⇒ normal ✓. Numerically: `‖[L_y, L_p]‖ ≤ 6e-15` and
`‖[L_{y²}, L_p]‖ ≤ 2e-15` for the spectral projections `p` of `a = x²` in `H₃(𝕆)`.
*Lean gap:* from "`y` op-commutes with every `χ_{>s}(a)`" to `y ∈ comm a` (every element of
`C(a)`). `opComm_of_sprojs` gives only `y | a`. For `f(a)` you need a uniform step-function
approximation `f(a) ≈ Σcᵢχ_{>sᵢ}(a)` (the pattern of `spectral_approx_expl`, but for `jbCfc a f`).
Routine, but it has to be written. Then
`b = y∘y ∈ comm a` by `jbw_mul_mem` ✓.

**Overall.** Hypothesis ⇒ `D(A) = 0` ⇒ (K') ⇒ `x | A` ⇒ `y | a` ⇒ `b ∈ comm a`. This proves
`JBSeqComm.mem_comm` for every JBW-algebra, with x = √a, y = √b; positivity is used only to
have the square roots. The proof in fact shows more: `U_xy² = U_yx² ⇒ y | x²` for *all*
self-adjoint x, y. Lean shopping-list additions: `‖exp D‖ ≤ 1`; `U_uU_v = U_{u∘v}` on `W(A)`;
comm-membership from the spectral projections. The JB case still needs `A**`.
