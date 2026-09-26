# B15 for Euclidean Jordan algebras: is a ⋄-self-adjoint root of a pure map pure?

Question (ERRATA, EJA 34/39; PLAN §2 "B15 recurs"): in an EJA `E`, let
`f : E → E` be positive, subunital and ⋄-self-adjoint (EJA 32), and let
`g = f ∘ f` be pure (EJA 18).  Is `f` pure?  If so, EJA 34 and EJA 39 hold for
⋄-positive maps in the sense of Def 32 literally (no purity asked of the root).

**Verdict: PROVED** (2026-09-26).  Lean: `Papers/EJA/PureRoot.lean`,
`diaSA_root_isPure`; corollaries `eja34'`, `eja39'`.

## Why the von Neumann proof does not transfer, and why it is not needed

The tree's B15 (`docs/B15-S.md`) splits into a *support* half (self-
contraposition gives `⌈f⌉ = ⌈f(1)⌉`) and a *determinism* half (2-positivity,
the Schur complement of `M₂(f)`, Gardner's theorem).  The second half has no
Jordan analogue (`docs/research/purity.md` §2: no `M₂`).  In finite dimension it
is replaced by linear algebra: a pure map is, on its corner, a *cone
isomorphism*, and a positive `T` whose square is a cone isomorphism of a
finite-dimensional cone is itself one (injective ⟹ bijective; the inverse is
`(T²)⁻¹ ∘ T`, positive).  Positive cone automorphisms of an EJA are
`Q_c ∘ Θ` with `Θ` a Jordan automorphism (EJA 36, `unital_order_iso_jordan`) —
no Kadison/Schur argument needed.  Routes (ii) (Peirce-½ Schur complement) and
(iii) (counterexamples on spin factors) were therefore not pursued; the
commutative case `ℝⁿ` was checked by hand as a sanity test (⋄-SA = symmetric
zero pattern; if row `i` of `f` has two non-zeros `j ≠ k` then `f²` has
`f²_{jj}, f²_{jk} > 0`, so `f²` is not a weighted partial permutation).

## The argument

Notation: `q = f(1)`, `s = ⌈q⌉`, `E_s = E₁(s)` (Peirce 1-space), `G = f ∘ f`.
Only two consequences of ⋄-self-adjointness are used, via the criterion
`t * f(p) = 0 ⟺ p * f(t) = 0` for idempotents `p, t` (`diaSA_iff`):

**(S) support.** At `p = 1`: `f^⋄(1) = f_⋄(1)` reads `⌈f(1)⌉ = im f`, so
`f(s) = f(1)`, i.e. `f(1 − s) = 0`.

**(K) killing.**  If `p` is an idempotent with `G(p) = 0`, then `p * f(1) = 0`
(hence `s ≤ 1 − p`).  Proof: `z := f(p)` is an effect with `f(z) = 0`, so
`f(⌈z⌉) = 0` (EJA 23 applied to `1 − z`: `f(⌊1 − z⌋) = f(1)`, and
`1 − ⌊1 − z⌋ = ⌈z⌉`).  Put `t = 1 − ⌈z⌉`: `t * f(p) = t * z = 0`, so by the
criterion `p * f(t) = 0`; and `f(t) = f(1)`.

**Step 1 (the pure square reflects order on its corner).**  `G` pure gives,
by the universal properties (EJA 24, 25, `corner_iso`, `filter_iso`),
`G = ξ_{q'} ∘ θ ∘ ι ∘ π_b` with `π_b` the standard corner (compression to
`E_e`, `e = ⌊b⌋`), `ι, θ` isomorphisms and `ξ_{q'} = Q_{√q'}` on `E_{⌈q'⌉}`,
which has the left inverse `Q_{b'}` (pseudo-inverse, `filter_data`).  Hence for
`x ∈ E_e`: `G(x) ≥ 0 ⟹ x ≥ 0` and `G(x) = 0 ⟹ x = 0`.

**Step 2 (`e = s`).**  `G(e) = G(1)` (compression), so `G(1 − e) = 0` and (K)
with `p = 1 − e` gives `s ≤ e`.  Conversely (S) gives `G(1 − s) = 0`;
`G(Q_e(1 − s)) = G(1 − s) = 0` (EJA 22), and `Q_e(1 − s) ∈ E_e` is positive,
so it is `0` by Step 1; thus `e * (1 − s) = 0`, `e ≤ s`.

**Step 3 (the root on the corner).**  By (S) and EJA 24, `f = f̄ ∘ π_s`
(`f̄ = f` restricted to `E_s`); `f̄(1) = q`, so by EJA 25 `f̄ = ξ_q ∘ T` with
`T : E_s → E_{⌈q⌉} = E_s` positive and unital (`ξ_q` injective, `ξ_q(1) = q`).
* `T` injective: `T c = 0 ⟹ f(c) = 0 ⟹ G(c) = 0 ⟹ c = 0` (Step 1, `c ∈ E_s = E_e`).
* `T` bijective: `E_s` is finite-dimensional.
* `T⁻¹` positive: for `d ≥ 0` and `c = T⁻¹ d`, `G(c) = f(ξ_q d) ≥ 0`, so
  `c ≥ 0` (Step 1).  `T⁻¹(1) = 1`.
So `T` is an isomorphism of `EJA_psu`, `ξ_q ∘ T` is a filter for `q` (a filter
precomposed with an isomorphism), and `f = (ξ_q ∘ T) ∘ π_s` is pure.  ∎

Remarks.  (a) Only (S) and (K) are used, i.e. ⋄-self-adjointness at `p = 1`
and at the idempotents killed by `G`; the full zero-pattern symmetry is not
needed.  Without some such condition the claim is false: on `ℝ³`,
`f(x) = x₁(e₂ + e₃)/2` is impure with `f ∘ f = 0` pure.  (b) For EJA 39 (`G`
faithful) the argument collapses to: `f` is a bijection with `f(E₊) = E₊`,
hence `Q_{√f(1)} ∘ Θ`.  (c) Finite dimension is used once (injective ⟹
surjective); the JBW-analogue would need the determinism half of B15.
