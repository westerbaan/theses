# Adversarial review: EJA 38 (main.tex:815) — verdict FALSE AS PRINTED (2026-09-26)

Reviewer brief: try to break the claim "EJA 38 is false as printed". Read from source:
Def. 32 (`f^⋄(p)=⌈f(p)⌉`, `f_⋄(q)=im(Q_q∘f)`, ⋄-self-adjoint iff `f^⋄=f_⋄`), Prop. 33
(the `⟨f(s),t⟩=0 ⟺ ⟨s,f(t)⟩=0` criterion), purity (filter ∘ corner, isos are both),
faithfulness (`im f = 1`), Lemma 38 and its proof (main.tex:815–889). No Lean.

## Statement (verbatim content)
`f : E → E` faithful, pure, ⋄-self-adjoint ⇒ `f = Q_{√f(1)} ∘ Θ` for some unital Jordan
iso `Θ` with `Θ(√f(1)) = √f(1)` and `Θ = Θ⁻¹`.

## The counterexample survives every attack
`E = ℝ ⊕ ℝ`, `q = (a,b)`, `0 < a ≠ b ≤ 1`, `Θ` = swap, `f = Q_q∘Θ`, `f(x,y) = (a²y, b²x)`.
* positive, subunital (`f(1) = (a²,b²) ≤ 1`), linear. ✓
* pure: `Q_q = ξ_{q²}` is the standard filter of the effect `q²` (`⌈q²⌉ = 1`, so no
  inclusion), swap is an iso hence a corner; filter∘corner. ✓ (Also: composite of pure maps, 31.)
* faithful: `f(x,y)=0`, `x,y ≥ 0` ⇒ `x=y=0`. ✓
* ⋄-self-adjoint in the paper's sense (Def. 32, computed directly, not via 33):
  idempotents `0,(1,0),(0,1),1`. `f^⋄(1,0) = ⌈(0,b²)⌉ = (0,1)`, `f^⋄(0,1) = (1,0)`.
  `f_⋄(1,0) = im(Q_{(1,0)}f) = im((x,y) ↦ (a²y,0)) = (0,1)`; symmetric for `(0,1)`;
  `f^⋄(0)=f_⋄(0)=0`, `f^⋄(1)=f_⋄(1)=1`. So `f^⋄ = f_⋄ = swap`. ✓
  (Note `f` is NOT trace-self-adjoint when `a≠b`; ⋄-s.a. is strictly weaker — Prop. 33 remark.)
* No freedom in `Θ`: `√f(1) = (a,b) = q` is invertible, so `f = Q_q∘Θ'` forces
  `Θ' = Q_q⁻¹ f = swap`. `Θ'(q) = (b,a) ≠ q`. The clause `Θ(√f(1)) = √f(1)` fails. ✓
  (`Θ = Θ⁻¹` does hold.) Arbitrary inner products on `ℝ⊕ℝ` change nothing: every
  step above is order/Jordan-theoretic.
Minimal: dimension 2 is the least possible (in `ℝ` the only unital iso is `id`).

## The broken step — agent's diagnosis confirmed
All steps up to `Θ Q_q Θ(q_i) = μ_i q_i` and `Θ(q²) = Σ μ_i q_i` are valid. Then
"by uniqueness of decompositions … `λ_j² = μ_j` and `Θ(p_j) = r_j` (ordered high to low)"
and "since the `λ_j²` and `μ_j` agree, the `p_j` and `r_j` agree" is the error: uniqueness
gives equal eigenvalue *sets* with `Θ(p_j)` = the `μ`-eigenprojection *for the same
value*, but `p_j` and `r_j` are indexed by different elements (`q²` vs `Θ(q²)`), so the
value `λ_j²` may sit on a different projection. In the example: `λ² = (a²,b²)` on
`(1,0),(0,1)`; `Θ(q²) = (b²,a²)`. The subsequent "Θ commutes with `Q_q`" and the
paper's derivation of `Θ = Θ⁻¹` (which uses that commutation) therefore also lose
their proof.

## Corrected statement (proof sketch; wants its own break-it pass before Lean)
**38′.** Under the same hypotheses, `f = Q_q ∘ Θ` with `q = √f(1)`, `Θ` a unital Jordan
iso, `Θ² = id`, and `Θ(q)` operator-commutes with `q`. (Example: `(b,a)` commutes with `(a,b)`.)
*Proof.* Valid part of the printed proof gives `Q_qΘ(q_i) = μ_i Θ⁻¹(q_i)` for any frame
`(q_i)` of primitive idempotents diagonalising `q`. Summing: `q² = Σ μ_i Θ⁻¹(q_i)`, so
`(Θ⁻¹q_i)` is a frame diagonalising `q²` (hence `q`), and `Q_q Θ⁻¹(q_i) = μ_i Θ⁻¹(q_i)`.
`Q_q` injective ⇒ `Θ(q_i) = Θ⁻¹(q_i)`. So `Θ(q) = Σ λ_i Θ⁻¹(q_i)` is diagonal in the
frame `(Θ⁻¹q_i)` that also diagonalises `q`: they operator-commute. Write `q' = Θ(q)`.
For `Θ² = id`: ⋄-s.a. reads `G∘Θ = Θ⁻¹∘G` on idempotents, `G(p) := ⌈Q_q p⌉`, i.e.
`⌈Q_{q'} Θ² p⌉ = ⌈Q_q p⌉` for all idempotents `p`. Put `h := Q_{q⁻¹} Q_{q'} Θ²`
(positive, invertible); then `⌈h(p)⌉ = p` for all idempotents `p`, so `h(e) = λ(e)e` on
atoms and `h` preserves central idempotents; on each simple factor of rank ≥ 2
linearity forces `λ` constant (checked by hand for spin factors: `λ(v) = λ(−v)`, and
`λ(v)+λ(−v)` independent of `v`), so `h = ` multiplication by a positive central `c`.
Then `Θ² = Q_{q'⁻¹} Q_q C = Q_w`, `w = q q'⁻¹ √c` (all commute), and `Θ²(1) = 1` gives
`w² = 1`, `w = 1`, `Θ² = id`. (The "h scalar on a simple factor" step is the weakest
link; it is standard for `M_n` and was checked for spin factors only.)

## Knock-on
* **EJA 39** (faithful pure ⋄-positive ⇒ `g = Q_{√g(1)}`): printed proof uses the false
  `Θ(q)=q`, so unproven as printed — but it is TRUE given 38′:
  `g = Q_qΘQ_qΘ = Q_q Q_{q'} Θ² = Q_q Q_{q'} = Q_{qq'}` (commuting ⇒ `qq' ≥ 0`, one-family
  law), `g(1) = (qq')²`, so `g = Q_{√g(1)}`. The example satisfies 39:
  `g = f² = (x,y) ↦ (a²b²x, a²b²y) = Q_{(ab,ab)}`. ✓ Agent correct.
* **EJA 34** (general pure ⋄-positive): reduces to 39 by corestriction; that reduction
  is untouched. Unproven as printed, restored by 38′.
* **EJA 40** (†-effectus): cites 34; same status. Not refuted.
* **`eja-dagger.md` §1 step 1** repeats the step verbatim ("yields `Θ(q) = q` …
  whence `Θ` commutes with `U_q` … gives `Θ = Θ⁻¹` … `U_q U_{Θq} Θ² = U_q²`"): that
  argument is wrong at `Θ(q) = q` and at `U_{Θq} = U_q`. Its conclusion `g = U_{√p}`
  survives via 38′ (`g = U_{q·Θq}`, not `U_{q²}`; `p = (q·Θq)²`, not `q⁴`).

## Verdict
FALSE AS PRINTED (confirmed). Minimal counterexample as above. Replace the clause
`Θ(√f(1)) = √f(1)` by "`Θ(√f(1))` operator-commutes with `√f(1)`"; `Θ = Θ⁻¹` survives
but needs the new proof above. 39/34/40: unproven as printed, true with 38′ (pending review
of the `h`-is-central step). Errata-worthy (a reader following 39's proof would stumble).
