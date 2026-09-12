# Quantitative effectus theory

Exploratory note (2026-09-12, Fable), unaudited.  Four themes, each with a
first statement, plausibility, refutation target and sketch.  Labels: `74IV`
(vn.tex `kaplansky`), `146VII`/`150II`/`158II` (dils.tex `dils-ultranorm`,
self-dual completion, `kaplansky-hilbmod`), `proc.tex` (⌈·⌉, ⌊·⌋, `asrt`,
⋄, quotients/comprehensions), `eff.tex` (`dagger-effectus`, `Kl(𝒟)`, `EJAᵒᵖ`).
An effectus map `f: X → Y` in `vNᵒᵖ` is an ncpsu map `Y → X`, `f^*(p)` its
action on predicates; `d(f,g) := ‖f − g‖_cb` in `vNᵒᵖ`, `sup_x TV` in
`Kl(𝒟)`, order-unit operator norm in `EJAᵒᵖ`.

Verdict: the one hard fact is that **the quantum `asrt` is exactly
½-Hölder, not Lipschitz** (§1.3); the same square root gives **approximate
comprehension with a √η loss** (§2.2).  Purity is not stable in any
⌈·⌉-based sense (§2.4); Kaplansky becomes "strong = weak + `&`" (§3);
object distances are discrete outside finite dimensions (§4).

## 1. Metric-enriched effectuses

**1.1 What is intrinsic.**  In a real effectus with separating states,
`Pred(X)` is an effect module; its enveloping order-unit space gives
`d(p,q) = inf{λ : p ≤ q + λ·1, q ≤ p + λ·1}` — the C*-norm in `vNᵒᵖ`, the
sup-norm in `Kl(𝒟)`, the order-unit norm in `EJAᵒᵖ`.  No new data on
predicates.  On maps the *plain* metric
`d₁(f,g) = sup_p d(f^*p, g^*p)` is intrinsic; the cb/diamond norm is not:
it needs ancillas `M_n ⊗ X`, and the effectus only supplies commutative
ancillas `n·X = ℂⁿ ⊗ X`.  Transpose-type examples give `d₁ ≠ d_cb`.  Hence:

> **Def.**  A *metric effectus* is an effectus with a metric `d` on every
> hom-set such that composition and `⊛` are 1-Lipschitz in each variable
> (enrichment in `Met` with the `ℓ¹` tensor), `[f,g]` is 1-Lipschitz,
> `d₁ ≤ d`, and `d(f,g) = d₁(f,g)` whenever `Y = 1` (states) or `X = 1`
> (predicates).  In a *monoidal* metric effectus require `d(f ⊗ id, g ⊗ id)
> = d(f,g)`.

`vNᵒᵖ` (cb), `Kl(𝒟)` (TV, here `d₁ = d`), `EJAᵒᵖ` (order-unit) satisfy
this by sub-multiplicativity of cb-norms.  Plausibility: high (bookkeeping).

**1.2 Lipschitz table (`vNᵒᵖ`).**

| construction | in its predicate | in its map |
|---|---|---|
| `f^*p` | 1-Lip in `p` | 1-Lip in `f` |
| `p^⊥`, `⊛`, scalar action | isometric / 1-Lip | — |
| `p & q = √p q √p` | ½-Hölder in `p` (sharp), 1-Lip in `q` | — |
| `asrt_p` | ½-Hölder (sharp, §1.3) | — |
| `⌈p⌉`, `⌊p⌋`, `f^⋄`, `f ↦ f^⋄` | discontinuous (`⌈ε1⌉ = 1`, `⌊(1−ε)1⌋ = 0`) | discontinuous |
| quotient `ξ_p`, comprehension `π_s` | the *object* `⌈p^⊥⌉X⌈p^⊥⌉` jumps | — |

`Kl(𝒟)`: the first four rows are 1-Lipschitz (`asrt_p` is multiplication
by `p`); the ⌈·⌉ row stays discontinuous.

**1.3 Theorem candidate (`asrt` is ½-Hölder, not Lipschitz).**
For effects `p, q` of a von Neumann algebra
`‖asrt_p − asrt_q‖_cb ≤ 2‖p − q‖^{1/2}`, and there are `p, q ∈ [0,1]_{M_2}`
with `‖asrt_p − asrt_q‖_cb ≥ 0.78·‖p − q‖^{1/2}` for arbitrarily small
`‖p − q‖`.  Consequently `p ↦ asrt_p` is Lipschitz on `[0,1]_𝒜` iff `𝒜` is
commutative.

*Sketch.*  Upper: `asrt_p − asrt_q = L_{√p−√q}R_{√p} + L_{√q}R_{√p−√q}`,
`‖L_xR_y‖_cb = ‖x‖‖y‖`, and `‖√p − √q‖ ≤ ‖p − q‖^{1/2}` (Ando/Kittaneh:
`‖f(A) − f(B)‖ ≤ f(‖A − B‖)` for operator monotone `f`, `f(0)=0`).
Lower: `p = e₁₁`, `q = (p + δ|w⟩⟨w|)/‖·‖` with `w = (1,1)/√2`.  Then
`‖p − q‖ ≈ 0.8δ`, while `√q` has a `√(δ/2)` entry in the `(2,2)` slot and
`(√q)e₁₂(√q) − p e₁₂ p` has a `√(δ/2)` entry: numerically the ratio
`‖asrt_p(e₁₂) − asrt_q(e₁₂)‖ / ‖p−q‖^{1/2}` is `0.786` for `δ = 10⁻¹…10⁻⁴`.
"Iff commutative": a noncommutative `𝒜` contains two non-commuting
projections; the von Neumann algebra they generate has an `M_2(ℂ)`
unital in a corner (Halmos), and the example lives there — the lower
bound only uses inputs from that copy.  Same statement in `EJAᵒᵖ` with
`asrt_p = Q_{√p}` (quadratic representation).

So the Lüders measurement depends on its effect only ½-Hölder-continuously,
and this *characterises* non-commutativity inside a metric `&`-effectus.
Risk: low (numerics above; the Halmos embedding is standard).

## 2. Approximate notions

**2.1 ε-sharp predicates are stable.**  Call `p` *ε-sharp* if
`‖p & p^⊥‖ ≤ ε` (effectus-intrinsic in an `&`-effectus; in `vNᵒᵖ` this is
`‖p − p²‖ ≤ ε`).  Then for `ε < ¼`, `d(p, Sharp(X)) ≤ ‖p − ⌊p⌋_{1/2}‖ ≤ 2ε`
where `⌊p⌋_{1/2}` is the spectral projection on `(½,1]`.  Holds in `vNᵒᵖ`,
`EJAᵒᵖ` (spectral theorem), `Kl(𝒟)` (pointwise).  Sharpness is Ulam-stable
although `⌊·⌋` is discontinuous: the discontinuity lives in the unsharp
region.  Plausibility: certain.

**2.2 Approximate comprehension (theorem candidate).**  Let `s` be sharp,
`π_s: {X|s} → X` its comprehension, and `f: Y → X` with
`f^*(s) ≥ 1 − η` (exact universal property: `f^*(s) = 1 ⇒ f = π_s ∘ g`).
Then there is `g: Y → {X|s}` with `d(f, π_s ∘ g) ≤ 2√η` (cb-norm), and
`√η` is optimal.

*Sketch (`vNᵒᵖ`).*  Write `f` as ncpsu `f: X → Y`, `s ∈ X`, `f(s) ≥ 1 − η`,
so `‖f(1 − s)‖ ≤ η`.  Put `g := f(s · s)`.  Cauchy–Schwarz for cp maps,
`‖f(x a)‖² ≤ ‖f(xx^*)‖·‖f(a^*a)‖`, applied to `f(a) − f(sas) =
f((1−s)a) + f(sa(1−s))` gives `‖f − g‖ ≤ 2√η`, and the same for
`f ⊗ id_n`, hence cb.  Optimality: the vector state `x = (√(1−η), √η)` on
`M_2`, `s = e₁₁`, has cross terms of size `√(η(1−η))`.
With 2.1: for ε-sharp `p` the comprehension of `⌊p⌋_{1/2}` is a
`2ε`-comprehension of `p` with the `2√η` universal property.  Plausibility:
high.

**2.3 Approximate quotient is exact for a perturbed predicate.**  If
`f^*(1) ≤ p^⊥ + η·1` then `f` factors *exactly* through `ξ_q` for
`q := (p − η)_+`, `‖p − q‖ ≤ η` — but `X/q` may be a strictly bigger corner
than `X/p`.  Exact for a nearby predicate at the cost of the object jumping; no √
loss, because quotient is output-side and comprehension input-side.

**2.4 Pure maps: closed but not stably characterised.**  In `vNᵒᵖ` the set
of pure maps `X → Y` is cb-closed.  Sketch: for `B(H) → B(K)` pure means
`a ↦ v^*av`; a cb-limit sends rank-one operators to rank-≤-1 operators
(rank is lsc), and a normal cp map with that property is `ad_v`.  General
`X, Y`: via `π ∘ ξ` in finite dimensions; direct integrals unargued.
The example `f_ε = (1−ε)·ad_V + ε·id`, `V` unitary non-scalar, shows
`d(f_ε, Pure) ≤ ε` with `f_ε` impure — no contradiction with closedness,
but it kills every *structural* ε-purity built on `⌈·⌉`/`⋄`: `f_ε^⋄ = id^⋄`
regardless of `ε`, so `⋄`-rigidity cannot see `ε`.  The only stable
ε-purity I can formulate is Choi-based (finite dimensions):
`‖C_f² − tr(C_f)·C_f‖ ≤ ε` implies `d_⋄(f, Pure) = O(nε)` (spectral gap),
and this needs `⊗`, not effectus structure.
So Ulam-stability of purity is true but not an effectus theorem; `f_ε`
refutes every ⌈·⌉-based candidate.

## 3. Kaplansky density as an effectus statement

**3.1 Strong = weak + `&`.**  For a bounded net of self-adjoints,
ultrastrong convergence `a_α → a` is equivalent to ultraweak convergence
of `a_α` and of `a_α²` (expand `ω((a_α − a)²)`).  In an `&`-effectus with
separating states this is intrinsic: on `Pred(X)` the *weak* uniformity is
`ω(p_α) → ω(p)` for all states `ω: X → 1`, the *strong* one additionally
`ω(p_α & p_α) → ω(p & p)`.
In `vNᵒᵖ` these are ultraweak and ultrastrong on `[0,1]_𝒜`; in `Kl(𝒟)`
the extra condition bites even classically (indicators oscillating around
`½` converge weak* to `½`, their squares not to `¼`).
`146VII`'s ultranorm is the same recipe with `⟨x, x⟩` in place of `p & p`.

**3.2 Effectus Kaplansky (conjecture).**  Let `S ⊆ Pred(X)` be norm-closed
and closed under `⊥`, `⊛`, scalars and `&`.  Then the weak closure of `S`
equals its strong closure, and it is `Pred` of a sub-object in the sense
that it is closed under all of the above and under weak limits.  In
`vNᵒᵖ` this is `74IV` for a C*-subalgebra and, since `&`-closed spans are
Jordan (`p∘q = ((p⊛q)² − p² − q²)/2` after rescaling), the JW-version
(Hanche-Olsen–Størmer §4.5) in general: the effectus statement is
*Jordan-natural*, consistent with `EJAᵒᵖ` being the other main model.
Plausibility: high; `Kl(𝒟)` is the commutative case.

**3.3 Kaplansky for maps (conjecture, the interesting one).**  Fix for
each vN algebra `𝒜` an ultraweakly dense unital C*-subalgebra `𝒜₀` and
let `vNᵒᵖ₀` be the sub-effectus of ncpsu maps with `f(𝒜₀) ⊆ ℬ₀`.  Then
every map of `vNᵒᵖ` is a pointwise-ultrastrong limit of maps of `vNᵒᵖ₀`
(equivalently: for every finite family of states `ω_i`, predicates `p_j`,
and `ε` there is `f₀ ∈ vNᵒᵖ₀` with `|ω_i(f₀^*p_j) − ω_i(f^*p_j)| < ε` and
the same for `p_j & p_j`).  Verified by hand in two cases:
`B(H)` with `K(H) + ℂ1`: for `f = ad_v` take `v_n = P_n v P_n + λ(1 − P_n)`
(finite-rank `P_n ↑ 1`), which is contractive, has `v_n^*v_n ∈ K + ℂ1`,
and `v_n → v` *-strongly; `L^∞[0,1]` with `C[0,1]`: mollify the kernel in
its first variable (Feller kernels are dense).  Refutation target: `𝒜₀ ⊆ B(H)` not
containing `K(H)` — the `v_n` trick uses `K ⊆ 𝒜₀`.  Risk: medium-high;
may need `𝒜₀ ⊇ K`-type hypotheses.  This is the honest form of "which
sub-effectuses are dense": density is a property of the *chosen* dense
C*-subalgebras, and there is no canonical choice.

## 4. Distances between objects

**4.1 Simulation distance.**  In a metric effectus put
`d_sim(X,Y) := inf_{f: X→Y, g: Y→X} max(d(g∘f, id_X), d(f∘g, id_Y))`.
A pseudo-metric (1-Lipschitz composition), iso-invariant, needs no `⊗` —
unlike a Wasserstein version, which needs couplings on `X ⊗ Y` *and* an
intrinsic cost between predicates of `X` and of `Y`; the effectus has
neither.

**4.2 Finite dimensions: quantumness is detected.**  `d_sim(M_n, M_m) > 0`
for `n ≠ m` (entanglement-fidelity bound `≤ m/n` for channels through
`M_m`), and `d_sim(M_2, ℂ^k) ≥ c > 0` for all `k`: a measure-prepare map
`Φ(a) = Σ ω_i(a)E_i` with `Σ E_i ≤ 1` cannot fix two non-commuting rank-one
projections `P_u, P_v` unless `|⟨u,v⟩| ≈ 0`.  So on finite-dimensional objects the zero set of `d_sim` is
isomorphism and `d_sim(X, classical)` is a no-broadcasting quantity.
Plausibility: high; the value of `d_sim(M_2, ℂ^k)` is open.

**4.3 Infinite dimensions: discrete.**  `d_sim(L^∞[0,1], ℓ^∞) ≥ 1`: a
`g∘f` through `ℓ^∞` is `a ↦ Σ_i k_i·μ_i(a)` with normal `μ_i`; choose `E`
of small measure inside `{Σ_{i>N} k_i < δ}` with `μ_i(E) ≤ δ` for `i ≤ N`,
then `‖(g∘f − id)(1_E)‖ ≥ 1 − 2δ`.  Same in `Kl(𝒟)` with the sup-TV metric:
`d_sim(n, m) = 1` for `m < n`.  So the cb/sup-norm simulation distance is
a finite-dimensional invariant; the infinite-dimensional theory must use
the uniformities of §3, i.e. "ε-finite representability": `X ≼_ε Y` iff
for every finite `F ⊆ Pred(X)` there are `f, g` with `‖(g∘f)^*p − p‖ ≤ ε`
on `F`.  `M_2 ⋠_ε ℂ^k` for small `ε` by 4.2, while `L^∞[0,1] ≼_ε ℓ^∞` for
all `ε` (conditional expectations onto fine partitions).  This is the
Gromov–Hausdorff-flavoured notion that survives; its zero set ("local
isomorphism") is strictly coarser than isomorphism.

## Best bets, ranked

1. §1.3 — `asrt` exactly ½-Hölder; Lipschitz iff commutative (numerically
   confirmed; Lean cost: `M_2` computation + Ando's inequality, absent
   from Mathlib).
2. §2.2 — approximate comprehension with sharp `2√η`; one Cauchy–Schwarz.
3. §3.1/3.2 — "strong = weak + `&`", Jordan-natural Kaplansky.
4. §4.2 — `d_sim` separates quantum from classical in finite dimension.
