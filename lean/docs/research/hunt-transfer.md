# Hunt: transfer principles and small models

Wild-hypothesis hunt (2026-09-12, no Lean, ~20 min).  Four bold conjectures, each attacked
concretely; KILLED with the killer, or SURVIVED with the sharpest test run.  Nothing here is
checked; every "holds" is a sketch.  Definitions are eff.tex's: quotient `ξ_p` with `1∘ξ_p ≤ p^⊥`
(3655), comprehension `π_p` with `p∘π_p = 1∘π_p` (3897), `⌊p⌋ = im π_p`, `⌈p⌉ = ⌊p^⊥⌋^⊥` (4177),
`p & q = q∘asrt_p` (4813), †-effectus via `dagger-theorem` (5300): unique `q` with `q&q = p`,
`asrt²_{p&q} = asrt_p asrt²_q asrt_p`, sharp quotients sharp.

## C1. Commutative transfer principle — KILLED, twice, and the surviving fragment is tiny

**Conjecture.** Every equation between terms in `⋎, ⊥, λ·, &, asrt, ⌈·⌉, ⌊·⌋, f^⋄, f_⋄, ξ, π, †`
that holds in `Kl(𝒟)` *and* in `Set` holds in `vNᵒᵖ`.

**Killer (shortest).** `p & q = q & p`: two variables, one operation; in `M_2` take
`p = |0⟩⟨0|`, `q = |+⟩⟨+|`: `p & q = √p q √p = ½ p ≠ ½ q = q & p`.  The map-level twin of the
same length: `asrt_p ∘ asrt_q = asrt_{p&q}` (true pointwise in `Kl(𝒟)`), false in `M_2` even
for *sharp* `p, q`: `asrt_p asrt_q (x) = pq x qp` while `asrt_{pqp}(x) = √(pqp) x √(pqp)`.
The direction is simply wrong: `Kl(𝒟) ↪ vNᵒᵖ` (`X ↦ ℓ^∞(X)`) is a full sub-⋄-effectus closed
under every operation above (corners, multiplication, supports of a commutative algebra are
computed inside it), so `vNᵒᵖ ⊨ E ⇒ Kl(𝒟) ⊨ E`, never the converse.

**Which fragment transfers?  Three refinements, two killed.**
* *Sharp ⋄-fragment* (`∧, ∨, ⊥, ⌈s & t⌉` on `SPred`): KILLED by the 2-variable orthomodular
  failure `s ∧ (t ∨ s^⊥) = s ∧ t` (`= ⌈s & t⌉`, the Sasaki hook), false for two non-orthogonal
  lines in `Proj(M_2)`, true in every Boolean `SPred` (`Set`, `Kl(𝒟)`).
* *`⌈·⌉`-fragment without `&`* (`⋎, ⊥, λ·, ⌈·⌉, ⌊·⌋`): KILLED by the same identity, because the
  fragment *defines* the lattice on sharps: `s ∨ t = ⌈½s ⋎ ½t⌉`, `s ∧ t = (s^⊥ ∨ t^⊥)^⊥`; put
  `s = ⌈p⌉, t = ⌈q⌉`.  (`⌈p ⋎ q⌉ = ⌈p⌉ ∨ ⌈q⌉` and `⌊p⌋ ⋎ ⌊q⌋ ≤ ⌊p ⋎ q⌋` do hold in every `vN`,
  the latter since `⌊p⌋ ≤ p ≤ q^⊥ ≤ ⌊q⌋^⊥`; equality in the latter fails already in `Kl(𝒟)`
  at `p = q = ½`, so it is not a transfer example.)
* *SURVIVED (sharpest test = the two above):* transfer holds for exactly (a) the **linear
  fragment** `⋎, ⊥, λ·` with any number of variables — `[0,1]_A` embeds, as an effect module,
  in `[0,1]^{S(A)}` via states, so identities of `[0,1]` hold pointwise; and (b) the **full
  signature in one predicate variable** (or any *commuting* family): `W*(p) ≅ L^∞(σ(p), μ)`
  is a commutative von Neumann algebra in which `⌈·⌉, ⌊·⌋, asrt, &, √` are all computed, and a
  one-variable identity in `L^∞` is a one-variable identity in the scalars `[0,1] = Pred(1)`.
  (b) is exactly Ozawa's transfer principle (commuting observables ⇒ classical truth values
  transfer) read inside the effectus.  So: **transfer dies the moment a second variable meets
  `&`, `⌈·⌉` or `⌊·⌋`; two variables plus anything non-linear already sees non-commutativity.**

**The Jordan test — `vNᵒᵖ` vs `EJAᵒᵖ`: KILLED, and the killer is a theorem.**  Conjecture:
`vNᵒᵖ ⊨ E ⇔ EJAᵒᵖ ⊨ E` (the `&`-equational theory does not see associative vs Jordan).  The
signature with scalars is polynomially complete for the Jordan structure on the positive cone:
`p∘_J q + ½(p² + q²) = 2 (½p ⋎ ½q)&(½p ⋎ ½q)` and `U_{√p}(q) = p & q`, so any Jordan polynomial
identity `P = 0` rewrites as `T_1 = T_2` in `⋎, λ·, &` (move the negative monomials across).
Now take Glennie's identity `G_8` (degree 8, three variables): it holds in every *special*
Jordan algebra — hence in every `vNᵒᵖ` (`[0,1]_A ⊂ A_sa`, special) and in `Kl(𝒟)`, `Set` — and
fails in the Albert algebra `H_3(𝕆)`; since the failure set is Zariski-open in `H_3(𝕆)^3` it
meets the interior of `[0,1]^3`.  So `G_8` is an equation in the effectus signature true in
`Kl(𝒟)`, `Set`, `vNᵒᵖ`, `CvNᵒᵖ`, `OUSᵒᵖ`-commutative parts, false in `EJAᵒᵖ`: **the
`&`-equational theory of effectuses distinguishes associative from Jordan, at 3 variables,
degree 8**; conversely `EJAᵒᵖ ⊨ E ⇒ vNᵒᵖ ⊨ E` only for identities checkable on `H_n(ℂ)`, which
is *not* automatic in infinite dimension (a 3-generated `W*`-algebra need not be RFD).

## C2. Census of ⋄-effectuses with `|Pred X| ≤ 4` — the "forced `Kl(𝒟_M)`" clause KILLED

**Effect algebras of size ≤ 4** are exactly four: `2 = {0,1}`, the 3-chain `C_2 = {0,a,1}`
(`a⊕a = 1`), the 4-chain `C_3 = {0,a,a^⊥,1}` (`a⊕a = a^⊥`), and the Boolean `2²`
(`a⊕a` undefined).  (`MO_2` has 6 elements; a 4-element `{0,a,a^⊥,1}` is a chain or `2²`.)

**Scalars.**  `M = Pred(1)` acts on `Pred X`; `λ ↦ λ·1_X` is an effect-algebra map, so `½`
would give `x` with `x ⊕ x = 1`, then `y ⊕ y = x`, ...; in a finite effect algebra such a chain
stabilises only at `0`, forcing `Pred X` trivial.  So **a non-trivial finite `Pred X` forces the
scalars to be finite, hence a Boolean algebra (eff.tex 644, basmsc prop. 40)** — and
`{0,½,1}` is *not* an effect monoid at all (`½ = ½⊙(½⊕½) = x⊕x` has no solution).  The seed's
`Kl(𝒟_{{0,½,1}})` does not exist; `Kl(𝒟_2) = Set` has Boolean predicates, so no `Kl(𝒟_M)` realises a chain.

**Lemma (Boolean ⋄-effectus sees only sharps through states).**  If `M = 2` then for a state
`ω` and predicate `p`, `p∘ω ∈ {0,1}`; `p∘ω = 1` makes `ω` factor through `π_p`, so
`⌊p⌋∘ω = 1`.  Hence `ω^*(p) = ω^*(⌊p⌋)`.  For `Pred X = C_2` or `C_3` the atoms `a, a^⊥` are
unsharp (`⌊a⌋ ∈ {0,a}` and `a` is not an image, see below), so `⌊a⌋ = ⌊a^⊥⌋ = 0` and
**`X` has no states at all**.  Any ⋄-effectus realising a chain is stateless on that object.

**Realisation (all four occur).**  `2`: `Set` on a point; `2²`: `Set` on two points.  Chains:
let `Chᵒᵖ ⊂ OUGᵒᵖ` be the full subcategory on the order-unit groups `(ℤ^k, (n_1,…,n_k))`
(product order).  It is closed under `0, 1 = (ℤ,1), +` (products of groups), so it is an
effectus (full subcategory of an effectus closed under the data; pullbacks and joint monicity
are inherited).  `Pred(ℤ^k, n) = ∏ [0,n_i]`, `Scal = Pred(ℤ,1) = 2`.  Computing in `OUG`:
* quotient of `p`: `X/p =` the order ideal generated by `p^⊥ = n − p`, with unit `p^⊥`, i.e.
  `(ℤ^{J'}, (n_i − p_i)_{i∈J'})`, `J' = {i : p_i < n_i}`, `ξ^* =` inclusion — universal since a
  positive `f^*` with `f^*(u) ≤ p^⊥` lands in that ideal;
* comprehension of `p`: the quotient group by the order ideal generated by `n − p`, which kills
  every coordinate with `p_i < n_i` (torsion-free: `n_i ≤ m(n_i − p_i)`), so
  `{X|p} = (ℤ^{J}, n|_J)`, `J = {i : p_i = n_i}`;
* image of `f^*: ℤ^k → ℤ^l`: `n` restricted to `{i : f^*(e_i) ≠ 0}` (torsion-free again), so
  `SPred = 2^k`, closed under `⊥`.
So `Chᵒᵖ` is a ⋄-effectus, `(ℤ,2)` has `Pred = C_2`, `(ℤ,3)` has `Pred = C_3` with `a = 1`,
`⌊1⌋ = ⌊2⌋ = 0`, `⌈1⌉ = ⌈2⌉ = 1`, `X/a = (ℤ,2)`, `{X|a} = 0`.  It is **not** an `&`-effectus:
no partial map `X ⇸ X` has `1∘f = a`, since `f^*(3) = 1` has no solution in `ℤ` — quotients and
comprehensions without a single assert.  Risk: low-medium (the `OUG` computations).
**Census answer: every effect algebra of size ≤ 4 is `Pred X` of some ⋄-effectus; the chains
only stateless, only with Boolean scalars, and never as a `Kl(𝒟_M)` or an `&`-effectus.**

## C3. "The effectus knows its scalars are `[0,1]`" — KILLED, then its refinement KILLED

**Conjecture.** A †-effectus with a faithful state on every object and separating predicates
has scalars a sub-effect-monoid of `[0,1]`.

**Killer 1 (Boolean/graded).**  `vNᵒᵖ_σ × vNᵒᵖ_σ` (σ-finite algebras): a †-effectus with all
axioms componentwise, faithful states `(ω_A, ω_B)`, separating predicates, scalars
`[0,1]² ∌ [0,1]` (zero divisors `(1,0)⊙(0,1) = 0`).  Equivalently `vNᵒᵖ` itself *is* such a
product once one looks at the non-factor `ℂ²` — the conjecture confuses `Pred(1)` with the
scalars of a factor.  Refine: add *connected scalars* (`SPred(1) = {0,1}`, no idempotents).

**Killer 2 (non-Archimedean, connected, totally ordered).**  Let `F = ℝ((t^ℚ))` (Puiseux
series), a real-closed non-Archimedean field, `M_P = [0,1]_F`.  `M_P` is a commutative,
totally ordered effect monoid with `0,1` its only idempotents, unique square roots (real
closed), and a divisoid (`a/b` field division, `0/0 = 0`).  By `new-monoidal` Prop 10
`Kl(𝒟_{M_P})_fin` is a ⋄-effectus; the `[0,1]`-proof that `Kl(𝒟)` is an `&`- and †-effectus
uses only square roots and division of scalars (pure maps = weighted partial injections, `†` =
transpose, `asrt_p = diag(p)`, axiom `asrt²_{p&q} = asrt_p asrt²_q asrt_p` is `p²q² = p²q²`,
sharp quotients are partial identities), so it goes through verbatim.  Faithful states: full-
support distributions on finite sets; predicates separate.  But `t ∈ M_P` is infinitesimal, so
every effect-monoid map `M_P → [0,1]` kills it: **no embedding**.  KILLED.  Risk: medium (the
`&`-uniqueness of `asrt_p` in `Kl(𝒟_M)` for non-Archimedean `M`).
*What the axioms do see:* `dagger-theorem`(1) applied to scalars forces unique square roots in
`M`, which kills the *simplest* non-Archimedean candidate `[0,1]` of the dual numbers `ℝ[ε]`
(`ε` has no square root, and it is not a divisoid).  So the † axiom is exactly "real closed",
never "Archimedean" — and by Tarski, `Kl(𝒟_{M_P})` and `Kl(𝒟)` satisfy the *same* first-order
sentences about scalars: a genuine transfer principle, in the direction nobody asked for.

## C4. Decidability and the free ⋄-effectus — one SURVIVED, one SURVIVED with a gap

**4a. The free ⋄-effectus on one stateless object `X` is the matrix category over `M` with a
phantom column — word problem trivial.**  SURVIVED.  Nothing forces a map `1 → X`, `Pred X =
M·1_X`, `SPred X = {0,1}`, `Hom(X,X) = M·id`; for divisoid `M` the quotient `X/λ` is `X` itself
with `ξ = λ^⊥·id` (universal property checked as in `Kl(𝒟_M)`), `{X|λ} = 0` for `λ ≠ 1`, so
adding quotients/comprehensions to `Kl(𝒟_M)_fin ⊔ {X}` creates no new object, and the initial
model of the essentially-algebraic theory is the category of `(m,k)×(n,l)` matrices with `M`
entries, `X→X` blocks scalar, `1→X` blocks zero.  Equality is decided by equality in `M`.  With
one *state* `ω: 1 → X` the collapse stops: `Hom(X,X) ∋ λ·id ⋎ μ·ω∘!`, a genuinely new monoid —
sharpest test not run: is that free `&`-effectus's `Pred X` still `M`?

**4b. The equational theory of `Kl(𝒟)` (map variables, full signature) is decidable.**
SURVIVED with a gap.  Fragments: pure composition — the free monoid embeds in stochastic
matrices (residual finiteness ⇒ transformation monoids), so no non-trivial monomial identities;
linear fragment `⋎, λ·, ∘` — distinct words act independently on the basis vector of the empty
word in the free-monoid representation, so identities are exactly the free "formal sums of
paths" of `new-monoidal` Thm 9 with generators, decidable by normal form; support fragment
`⌈·⌉, f^⋄, ∨` — `(g∘f)^⋄ = f^⋄ g^⋄` reduces it to identities of binary relations under
`∘, ∪, id`, the theory of idempotent semirings (Andréka–Bredikhin), decidable.  The *gap* is
the mixed fragment with `⌊·⌋` (thresholds "`= 1`", i.e. linear equations inside supports):
no bounded-counterexample-size lemma; the natural route (evaluate in `Kl(𝒟_{M_P})`, Tarski)
needs a size bound on witnessing sets, which composition destroys.  Sharpest test: find a mixed
identity whose smallest counterexample grows with term depth.  Not found.
**Contrast:** the same theory for `vNᵒᵖ` contains the sequential-product identities
(`p & (p & q) = p² & q`, Glennie), and for all `M_n` at once no size bound exists even for the
associative product (Amitsur–Levitzki: `s_{2n}` fails first at `M_n`), so decidability of the
`&`-equational theory of `vNᵒᵖ` is genuinely open and probably hard.
