# Hunt: homological invariants of an effectus

Wild-hypothesis hunt, 2026-09-12. No Lean, unaudited hand computations. Killers:
`M_n`, `ℓ^∞(X)`, `B(H)`, II₁/II∞/III, `ℂ ⊕ M₂`, `Kl(𝒟)` on 3 points, `Set`, `V_m`, `ℍ_n(ℝ)`, `ℍ₃(𝕆)`.
Vocabulary: `SPred(X)` sharp predicates; `≈` the symmetry-exchange relation of
`eja-dagger.md` §4 (`p ≈ q` iff a finite chain of the canonical symmetries
`σ_g = ad_{2g−1}` / `U_{2g−1}` carries `p` to `q`; unitary equivalence in `vNᵒᵖ`,
equality in `CvNᵒᵖ`, `Kl(𝒟)`, `Set`).

## H1. `K₀` of an effectus — SURVIVED (with one seed error killed)

Seed says "⋎ as addition"; that is not a monoid: on `M_n` the classes `[1],[1]`
cannot be orthogonalised (no `M₂ ⊗ −` in a bare effectus). Fix, no tensor needed:

> `K₀^≈(X)` := universal abelian group of the effect algebra `SPred(X)` (generators
> `[s]`, relations `[s ∨ t] = [s] + [t]` for `s ⊥ t`) modulo `[p] = [q]` for `p ≈ q`.

**Conjecture H1.** In `vNᵒᵖ`, `K₀^≈(𝒜) ≅ K₀(𝒜)` via `[p] ↦ [p]`.
Tests passed: `M_n`: `SPred/≈ = {0..n}`, group `ℤ` ✓. `ℓ^∞(X)`: `≈` is equality,
universal group of `2^X` = bounded `ℤ`-valued functions = `K₀(ℓ^∞(X))` ✓ (also for
infinite `X`). II₁ factor: `≈` = MvN (finite algebra), classes `τ(p) ∈ [0,1]`,
universal group of the interval effect algebra = `ℝ` ✓. `ℂ ⊕ M₂`: `{0,1}×{0,1,2}`,
`ℤ²` ✓. `B(H)`: `1 = p ∨ p⊥` with `p ≈ p⊥` (both infinite rank and corank) gives
`[1] = 2[p]`; `p = p₁ ∨ p₂` with `p₁ ≈ p₂ ≈ p` gives `[p] = 0`, then rank-one `e`
has `[1] = [p_{∞,1}] + [e]` with `p_{∞,1} ≈ ... = 0`, so `K₀^≈ = 0 = K₀(B(H))` ✓.
Type III: all nonzero projections `≈`, so `[1] = 2[1] = 0` ✓.
**Seed error killed:** `K₀` of a II∞ factor is `0`, not `ℝ` (the dimension monoid
`[0,∞]` has `∞ + x = ∞`, so its Grothendieck group is trivial; II∞ is properly
infinite); `K₀^≈` agrees: same halving argument as `B(H)`.
Open (sharpest untested point): injectivity of `K₀^≈ → K₀` for non-σ-finite
properly infinite algebras, where `≈` (unitary) is coarser than MvN and the
halving arguments need Kadison–Ringrose 6.3.4-style comparison. Risk: moderate.

`Kl(𝒟)`, 3 points: canonical symmetries are trivial, so `K₀^≈ = ℤ³` ✓ (seed).
Definitional fork: if *all* involutive automorphisms (transpositions) count as
symmetries, `≈` = equal cardinality and `K₀^≈ = ℤ` — only `|X|` survives. Record
which `≈` is meant before anyone builds this. `Set`, `X` infinite: `0`, the exact
analogue of `B(H)` (`ℵ₀ + ℵ₀ = ℵ₀`).

**"Something new for `EJAᵒᵖ`" — KILLED.** Products of `U_{2g−1}` are transitive on
idempotents of fixed rank in every simple EJA (`Inn`, cf. eja-dagger §4), so
`SPred/≈ = {0..rank}` and `K₀^≈(simple) = ℤ`: the Albert algebra gives `ℤ` like
`M₃`, every spin factor `ℤ` like `M₂`, general `E` gives `ℤ^{#simple summands}`.
`K₀^≈` sees neither `𝕂` nor the spin/Albert type — exactly the Morita class of
`new-morita.md` S7. Consistent, not new. (Corollary worth keeping: `K₀^≈` is a
(D1)-Morita invariant in all three worlds; tested `pRp` vs `R`, `τ(p) = ½`: `ℝ ≅ ℝ`.)

## H2. Quotient/comprehension as a short exact sequence — one half KILLED, one SURVIVED

Seed's sequence `{p⊥} → X → X/p` is wrong-headed: in a †-effectus `{p⊥} ≅ X/p`
and `ξ_p ∘ π_{p⊥}` is an iso, not zero. The sequence with content is

> `{p} →π_p X →ξ_p X/p`, `ξ_p ∘ π_p = 0`.

**Claim (SURVIVED, cheap).** In `Par(C)`, `π_p` is the kernel of `ξ_p`
(`ξ_p ∘ f = 0 ⟺ p⊥ ∘ f = 0 ⟺ p ∘ f = 1 ∘ f ⟺ f` factors through `π_p`, by the
comprehension property) and, for sharp `p`, `ξ_p` is the cokernel of `π_p`
(`g ∘ π_p = 0 ⟺ π_p^*(1∘g) = 0 ⟺ 1∘g ≤ p⊥ ⟺ g` factors through `ξ_p`; the middle
step is `pqp = 0 ⟺ q ≤ p⊥` in `vNᵒᵖ`, needs eff's sharp-orthogonality lemma in
general). So quotient/comprehension pairs are kernel–cokernel pairs. Risk: low.

**Exact/Puppe-exact structure — KILLED.** Quillen-exact needs additivity; `Par(vNᵒᵖ)`
is only partially additive. Puppe-exact needs every map to be cokernel-then-kernel:
the depolarising channel on `M_n` has full support and full image, so its
"cokernel–kernel" factorisation is `id ∘ f ∘ id`, and `f` is no iso. Dead.

**Euler characteristic.** `dim Pred` is not additive (seed: `k² + (n−k)² ≠ n²`).
What is additive is rank (= `[1_X] ∈ K₀^≈`, trivially, `p ∨ p⊥ = 1`). The *defect*
is the interesting number:
    `δ(X;p) := dim Pred(X) − dim Pred({p}) − dim Pred(X/p)`
`= 2 dim(pMp⊥) = 2k(n−k)` on `M_n`; `= dim V½(p) = d_𝕂·k(n−k)` on `ℍ_n(𝕂)`
(`d = 1,2,4,8`); `= m−1` on `V_m` with `p` minimal; `= 0` on `Kl(𝒟)`, `ℓ^∞`.
Conjecture H2′: `δ(X;p) = 0 ⟺ p` central (`X ≅ {p} + X/p`) — true in `vNᵒᵖ`
(`pMp⊥ = 0`) and `EJAᵒᵖ` (`V½(p) = 0 ⟺ p` central). SURVIVED, but it is the Peirce
decomposition in disguise, not homology. The bolder "δ = (field dim)·rank·corank"
is KILLED by `V₄` (`δ = 3`, no field of dimension 3).
"Topological χ of the atom space is additive": KILLED by `ℍ₂(ℝ)`: atoms `ℝP¹ = S¹`,
`χ = 0`, but `{p}`, `X/p` are both `ℝ` with `χ = 1 + 1 = 2`. (For `M_n`: `ℂP^{n−1}`,
`χ = n`, additive — the complex case hides the failure.)

## H3. Betti/Möbius numbers from the ⋄-calculus — SURVIVED, the best find

For `f : X → X` let `L_f := {s ∈ SPred(X) : f^⋄ s ≤ s}` (a complete sublattice:
`f^⋄` preserves `∨`, and `f^⋄(s∧t) ≤ s∧t`). Define `b(f) := μ_{L_f}(0,1)` when
`L_f` is finite, else the reduced Euler characteristic `χ̃` of the order complex of
`L_f ∖ {0,1}` with the topology the scalars induce on predicates (`new-metric.md`).

**H3a (`Kl(𝒟)`, Markov chains).** `L_f` = forward-closed subsets = up-sets `J(P)` of
the poset `P` of communicating classes. Möbius of `J(P)`: `μ(∅,P) = (−1)^{|P|}` if
`P` is an antichain, else `0`. So `b(f) ≠ 0 ⟺` every state is recurrent, and then
`b(f) = (−1)^{#ergodic components}`. On 3 points: the cycle `1→2→3→1` gives `−1`;
`1→2, 2→3, 3→3` gives `L = {∅,{3},{2,3},X}`, a chain, `b = 0`. Falsifiable, checked.

**H3b (`vNᵒᵖ`, automorphisms).** `f = ad_u` on `M_n`: `L_f` = direct sums of subspaces
of eigenspaces, so `L_f ≅ Π_i Gr(ℂ^{m_i})` and `b` is multiplicative. Topological
Möbius of the full subspace lattice of `ℂ^n`: the order complex is the homotopy
colimit of partial flag manifolds, `χ = Σ_{k≥2} (−1)^k k!·S(n,k) = 1 + (−1)^n`
(multinomials = `χ` of partial flags; checked by hand `n = 2,3,4`), so
`b(ad_u) = (−1)^n` for every unitary `u`, the Boolean value of `ℓ^∞(n)`.
Amplitude damping on `M₂`: `L_f = {0, e, 1}` a chain, `b = 0`. Dephasing: `L_f = 2²`,
`b = 1`. So `b` is a Lefschetz-type number: `0` for dissipative maps, `±1` for
"recurrent" ones. One direction is a theorem: **Crapo's complementation theorem**
gives `b(f) ≠ 0 ⇒ L_f` complemented (every `f`-invariant `s` has an `f`-invariant
complement). Conjecture: the converse holds in `vNᵒᵖ` and `Kl(𝒟)` (true in `Kl(𝒟)`:
`J(P)` complemented iff `P` antichain iff Boolean). Risk: moderate.

**H3c (`EJAᵒᵖ`: the field is visible).** For `f = id`, `b(X) = χ̃(SPred(X)∖{0,1})`:
- `V_m`: proper part = atoms `S^{m−1}`, `b = (−1)^{m−1}`: `ℍ₂(ℝ) = V₂ ↦ −1`,
  `ℍ₂(ℂ) = V₃ ↦ +1`, `ℍ₂(ℍ) = V₅ ↦ +1`, `V₄ ↦ −1`.
- `ℍ₃(ℝ)`: `χ = χ(ℝP²) + χ(ℝP²) − χ(Fl₃(ℝ)) = 1 + 1 − 0 = 2`, `b = +1`.
- `ℍ₃(ℂ)`, `ℍ₃(ℍ)`, `ℍ₃(𝕆)`: `3 + 3 − 6 = 0` (`Fl₃(ℂ)`, `Sp(3)/Sp(1)³`,
  `F₄/Spin(8)` all have `χ = 6`), `b = −1`.
- `ℍ₄(ℝ)`: real partial-flag `χ` = `q`-multinomials at `q = −1`: `2`, `b = +1`.
**Conjecture H3c.** `b(ℍ_n(𝕂)) = (−1)^n · q_𝕂^{n(n−1)/2}` with `q_ℝ = −1`,
`q_ℂ = q_ℍ = q_𝕆 = 1` — the Möbius function of the subspace lattice over `F_q`,
`(−1)^n q^{n(n−1)/2}`, evaluated at `q = ±1` (real Grassmannians have
`χ = [n choose k]_{q=−1}`). Passed every case above. This is a †-effectus invariant
(given the metric topology on predicates) that separates `ℍ_n(ℝ)` from `M_n`, which
`K₀^≈`, Morita (S7), the scalars (`new-base.md`) and `Out` cannot. Direct sums:
`b(ℂ ⊕ M₂) = (−1)(+1) = −1` (Möbius is multiplicative on products). Even spin factors
`V_{2k}` behave "real", odd ones "complex" — the `b`-invariant of a spin factor is
the parity of `m`. Caveat: the topology on `SPred(X)` must be effectus-definable;
`new-metric.md`'s `p ↦ asrt_p` cb-distance is the candidate. Risk: moderate.

## H4. `K₁` from †-unitaries modulo symmetries — KILLED

`K₁^eff(X) := Aut(X)/⟨σ_g⟩`. `M_n`: `Aut = PU(n)`, symmetries generate
`{det = ±1}`, whose image is all of `PU(n)`, so `K₁^eff = 1 = K₁(M_n)` ✓. II₁ factor
(Broise: every unitary is a finite product of symmetries) and properly infinite
(Fillmore, four symmetries): `K₁^eff = Out(M)`. `ℓ^∞(X)`: symmetries trivial,
`K₁^eff = Sym(X) ≠ 0 = K₁(ℓ^∞(X))` — non-abelian, wrong. Killer: `ℓ^∞(3)`. In every
case it is `Out(M)` (or `Aut`), already S11 of `new-morita.md`. Topological `K₁` of any von Neumann
algebra is `0` (`U(𝒜)` norm-connected): the only honest effectus `K₁` is `0`.

## H5. Cohomology of the scalar effect monoid — KILLED

Scalars are `[0,1]` in `vNᵒᵖ`, `EJAᵒᵖ`, `Kl(𝒟)` alike. Any invariant of the scalar
monoid alone takes one value on `M_n`, `ℓ^∞`, II₁, `ℂ ⊕ M₂`, `Kl(𝒟)`, the Albert
algebra (`new-base.md`: no scalar axiom sees the field). Only per-object phase groups
`Φ(s)` (`new-monoidal.md`) carry content.

## Ranking

1. H3 (`b(f)`, `L_f` Möbius): recurrence ⟺ `b ≠ 0` in `Kl(𝒟)` (theorem-grade),
   Crapo as the general half; `b = (−1)^n q_𝕂^{n(n−1)/2}` separates real from complex.
2. H1 (`K₀^≈` = universal group of `SPred` mod symmetries): matches `K₀(𝒜)` on
   every tested algebra including the corrected II∞ = 0; `ℤ^X` on `Kl(𝒟)`; only the
   Morita class on `EJAᵒᵖ`.
3. H2: `(π_p, ξ_p)` is a kernel–cokernel pair in `Par(C)`; the additivity defect of
   `dim Pred` is the Peirce-½ dimension and vanishes iff `p` is central.
