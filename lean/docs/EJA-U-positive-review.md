# Adversarial review of `docs/EJA-U-positive.md`

**Verdict: certified with four named repairs.**  Every step was re-derived from
the axioms in `Theses/B/Eff/JordanAlgebras.lean` (class at l. 265: comm., unital,
Jordan, finite-dimensional, formally real, `≤` = sums of squares), not from the
document's summaries.  No step needs Macdonald, Shirshov–Cohn or the fundamental
formula; the mathematical core is smaller than advertised, not larger.  Nothing
here is a B15-style hole: no claim is false, but two cited justifications do not
justify what they are attached to, and one hypothesis (`t ≥ 0`) makes §4 not
follow from §1 as written.

## 1. The pivot identity — correct, one unlisted ingredient

`U_g = 2L_g² − L_{g²} = 2L_g² − L_g = ejaPone g` for `g² = g`, so `U_g q ∈ V₁(g)`
is definitional (`eja_mul_pone`), not a fact needing proof.  `U_g g = g`, and
`ejaB_pone_self_adj` gives `B(U_g q, g) = B(q, U_g g) = B(q,g)`, so
`σ = B q g / B g g` with `B g g = ejaTrL g > 0` (`eja_tr_idem_pos`).  ✔

Expanding with `g = c+z+d`, `q*g = c + ½z`, `c*d = 0`, `P½(z²) = 0`:

    2 g*(g*q) − g*q  =  [2c² + P₁(z²) − c] + [3(c*z) + (d*z) − ½z] + [P₀(z²)]

**Repair R1.**  The `V₁` part reduces to `c − P₁(z²)` by `c = c² + P₁(z²)`, as the
document says; but the `V½` part reduces to `2(c*z)` **only** via the *third*
component of `g*g = g`, namely `z = 2(c*z) + 2(d*z)`, which the proof does not
list among its ingredients (it lists only the `V₁` and `V₀` components).  With
the listed facts alone the display on line 31 is `3(c*z) + (d*z) − ½z`, not
`2(c*z)`.  The relation is of course available; the ingredient list is what is
wrong, and a Lean formalisation guided by that list will stall here.

Given it, matching against `σ(c+z+d)` yields all five relations, each of which I
re-derived: `c² = σc` (from `c − P₁z² = σc` and `c = c² + P₁z²`),
`P₁z² = (1−σ)c`, `P₀z² = σd`, hence `z² = (1−σ)c + σd`; `d² = (1−σ)d` from
`d = d² + P₀z²`; `2(c*z) = σz`; and `2(d*z) = (1−σ)z` from the `V½` relation.  ✔

`P½(z²) = 0` from **one** instance of `eja_lin` is exact: `eja_lin q z z q` gives
`q*(q*z²) − z²*q + ¼z² − ¼z² + ¼z² − ¼z² = 0`, i.e. `L_q² z² = L_q z²`, i.e.
`P½ z² = 4L_q z² − 4L_q² z² = 0`.  ✔  `c*d = 0` and `c*z, d*z ∈ V½` check out
verbatim against `eja_commute_of_peirce_one/zero` (l. 3380/3387).  ✔

**Repair R4 (justification, not content).**  `0 ≤ σ ≤ 1` is claimed from "both
pairs in the cone", i.e. self-duality of the cone — which is *not* in the tree
and whose usual proof runs through the very positivity being proven.  Two clean
substitutes exist: (a) `eja_isSumSq_ejaB_idem_nonneg` (l. 1344, `0 ≤ B z p` for
`z` a sum of squares and `p` idempotent) applies directly, since `g = g*g` and
both `q` and `1−q` are idempotents; or (b) cheaper still, `ejaLm_eq_peirce` gives
`B q g = B(g, L_q g) = B(c,c) + ½B(z,z)` and `B g g = B(c,c)+B(z,z)+B(d,d)`, so
`σ = (‖c‖² + ½‖z‖²)/‖g‖² ∈ [0,1]` with no cone theory at all.

## 2. `f² = μf` — correct as printed

`f = c + tz + t²d`, `c*d = 0`:
`f² = c² + t²z² + t⁴d² + 2t(c*z) + 2t³(d*z)`
`= [σ+t²(1−σ)]c + [tσ+t³(1−σ)]z + [t²σ+t⁴(1−σ)]d = μf`, `μ = σ+t²(1−σ)`.
Every cross term checked; the omitted `2t²(c*d)` is zero.  `μ > 0 ⇒ μ⁻¹f`
idempotent `⇒ 0 ≤ f` (`eja_idem_nonneg`); `μ = 0 ⇒ B f f = ejaTrL 0 = 0 ⇒ f = 0`
by positive definiteness.  ✔

**Repair R3.**  The hypothesis `t ≥ 0` (line 17) is never used and must be
dropped: `μ ≥ 0` for **all real** `t`.  As stated, the lemma does not support
§4's first corollary (`λ < 0` needs `t = 1/λ < 0`, see §3 below) nor its second
(`α + tβ + t²γ ≥ 0` for `t > 0` only gives `β ≥ −2√(αγ)`; the two-sided
`β² ≤ 4αγ` needs negative `t` as well).  Costless repair, real gap as printed.

## 3. `U_{λq+μ(1−q)} = λ²P₁ + λμP½ + μ²P₀` — correct

`L_q = P₁ + ½P½`, `L_{1−q} = P₀ + ½P½`, so `L_a = λP₁ + ½(λ+μ)P½ + μP₀` and, with
`a² = λ²q + μ²(1−q)`, `L_{a²} = λ²P₁ + ½(λ²+μ²)P½ + μ²P₀`.  Then
`2L_a² − L_{a²} = λ²P₁ + ½[(λ+μ)² − λ² − μ²]P½ + μ²P₀ = λ²P₁ + λμP½ + μ²P₀`.  ✔
`λ = 1, μ = t` gives `U_{q+t(1−q)}g = c + tz + t²d = f`.  ✔  For `λ ≠ 0`,
`U_{λq+μ(1−q)} = λ²·U_{q+(μ/λ)(1−q)}`; `λ = 0` is `μ²P₀` (`eja_pone_nonneg` at
`1−q`).  In §3(d) `U_{d₁}` uses `t = 1/λ`, hence R3.

## 4. Globalisation — sound

(b) is fine: `EJACorner` carries a full EJA instance (l. 3611), `eja_spectral`
there splits any `x ∈ V₁(e) \ ℝe`, and `V₁(p) ⊊ V₁(e)` because `e ∈ V₁(p)` would
force `p = e`; the same for `e−p`, so the recursion on `dim V₁` is well founded.
Orthogonality of the resulting primitives holds but is **not needed**: (c) only
needs each `eᵢ` to be *some* sum of primitives, after which linearity of `U_a`
and convexity of the cone finish.  No closure issue arises — `eja_spectral`
produces an exact finite decomposition with `Σ eₗ = 1`, so "closed cone" versus
"generated cone" never has to be argued.

(d) I verified `U_a = U_{d₁} ∘ U_{d₂}` on each Peirce space of `c`
(`a = λc + a'`, `c*a' = 0`, `A = L_{a'}|V½`):
`V₁`: `λ²` both sides.  `V₀`: `U_{a'}` both sides.  `V½`: `U_a = 2λA + (2A² −
L_{a'²})` and `U_{d₁}U_{d₂} = λ(2A + 2A² − L_{a'²})`, equal iff `2A² = L_{a'²}`.
Only Peirce multiplication rules are used — no Macdonald, as claimed.  ✔
Induction measure: `d₂ = c + a'` trades the spectral value `λ` for `1`, and
`eja_spectral` normalises `Σ eₗ = 1`, so the count of values `≠ 1` drops by one
and the base case really is `a = 1`, `U_1 = id`.  ✔

**Repair R2.**  The extra lemma "`U_{a'}` kills `V½(c)`" is true, but the cited
instance `eja_lin a' a' c y` is **inert**: all four mixed terms vanish
(`a'*c = 0`) and it collapses to `c*(a'²*y) = ½a'²*y`, which is just
`a'² ∈ V₀ ⇒ a'²*y ∈ V½`.  The instance that works is `eja_lin a' a' y c`:
terms 2,4,5 vanish (`a'*c = 0`, `a'²*c = 0`), 1 and 3 coincide, and using
`c*(a'*y) = ½(a'*y)` it reads `2·a'*(½(a'*y)) − ½a'²*y = 0`, i.e.
`2a'*(a'*y) = a'²*y`, i.e. `U_{a'}|V½(c) = 0` — one line, not the budgeted ≈40.

## 5. Sanity check redone: spin factor

`V = ℝ⊕ℝⁿ`, `q = ½(1,e)`, `g = ½(1,s)`, `ρ = s·e`.  `V₁(q) = ℝ(1,e)`,
`V₀(q) = ℝ(1,−e)`, `V½(q) = {(0,u) : u ⊥ e}`.  Splitting `s = ρe + s⊥`:
`c = ((1+ρ)/2)q = σq`, `d = ((1−ρ)/2)(1−q) = (1−σ)(1−q)`, `z = (0, ½s⊥)`, and
`σ = B q g / B g g = (1+ρ)/2` ✔ (matches line 49).  Then `c² = σ²q = σc` ✔;
`d² = (1−σ)d` ✔; `z² = (¼|s⊥|², 0) = ((1−ρ²)/4)·1 = σ(1−σ)·1 = (1−σ)c + σd` ✔
(the `q + (1−q) = 1` collapse is a genuine, non-trivial confirmation of the
coefficients);  `2c*z = 2σ(q*z) = σz` ✔; `2d*z = (1−σ)z` ✔.  All five relations
confirmed independently.  The `Sym_n` check (`DvvᵀD = |Dv|²·rank-one`, `σ = v₁²`) also checks out.

## 6. Residue

§5 is sound as far as it is load-bearing: `σ_q = P₁ − P½ + P₀` is an
automorphism (the `ℤ/2` Peirce grading), giving `|β| ≤ α+γ`, the AM–GM weakening
of the wanted bound; `T_sT_t = T_{st}` is immediate from orthogonality.  §4's
second corollary additionally needs the unstated step "general idempotent `g` =
sum of primitives, `U` linear".  Cost: §3(d) is over-budget by the ~40 lines
assigned to the `V½` lemma (R2); §1's estimate stands.
