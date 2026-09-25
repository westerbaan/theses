# Errata in the follow-up papers

One section per paper (tag as in `lean/Papers/README.md`); one entry per point, citing the point number, the print, the problem, the repair and the Lean witness.

## OAP — *A characterisation of ordered abstract probabilities* (arXiv:1912.10040, `1912.10040/first.tex`)

* **OAP 2** (`ex:orthomodularlattice`, first.tex:390, Example) — **false as printed.**
  The print makes an orthomodular lattice an effect algebra with
  `x ⊥ y ⟺ x ∧ y = 0`.  Complements are then not unique: in `MO2` the atoms
  `a`, `b` have `a ∧ b = 0` and `a ∨ b = 1`, yet `b ≠ a^⊥`.  Repair:
  `x ⊥ y ⟺ x ≤ y^⊥` (the two agree in a Boolean algebra, which is the only
  case the paper uses, Example 6).  Lean: `Papers.OAP.oap2_false_as_printed`
  (refutation), `Papers.OAP.oap2_le_iff` (repaired claim).
* **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), third clause —
  **false as printed.**  For `S ⊆ [x,1]` the print reads
  "`⋀_{s∈S} s ⊖ x` exists ⟹ `(⋁S) ⊖ x = ⋁_{s∈S} s ⊖ x`"; the premise must be
  `⋁_{s∈S} s ⊖ x` (a supremum).  As printed it fails already for `x = 0`: in
  the Wright triangle `{a₁, a₂}` has infimum `0` but no supremum.  Lean:
  `Papers.OAP.oap24_3_false_as_printed` (refutation), `Papers.OAP.oap24_3`
  (corrected clause).
* **OAP 22** (`lem:forcing`, first.tex:727, Lemma), proof, first line — typo:
  "Since `a ≤ a'` and `b ≤ b'`" should read "Since `a ≤ b` and `a' ≤ b'`".
  Statement unaffected (`Papers.OAP.oap22_forcing`).
* **OAP 43** (`thm:multisnormal`, first.tex:1525, Theorem), proof — gap.
  The theorem claims that `⋁_{s∈S} b·s` *exists*; the printed chain
  `(b ⋁ ⌈b⌉^⊥)·⋁S = ⋁_s (b ⋁ ⌈b⌉^⊥)·s ≤ ⋁_s b·s ⋁ ⋁_{s'} ⌈b⌉^⊥·s' ≤ …`
  already uses `⋁_s b·s` (and `⋁_{s'} ⌈b⌉^⊥·s'`) as existing, so the forcing
  argument only shows the two agree *once both exist*.  (The proof also
  reuses the name `b'` for `b ⋁ ⌈b⌉^⊥`, clashing with the `b'` of the
  statement.)  Repair: for an upper bound `u` of `b·S` put
  `u' = u ∧ b·⋁S` (Theorem 37); then `u' ≤ ⌈b⌉`, so `u' ⊥ ⌈b⌉^⊥·⋁S`, and
  `b·s ⋁ ⌈b⌉^⊥·s ≤ u' ⋁ ⌈b⌉^⊥·⋁S` for all `s` gives
  `b·⋁S ⋁ ⌈b⌉^⊥·⋁S ≤ u' ⋁ ⌈b⌉^⊥·⋁S`, whence `b·⋁S ≤ u' ≤ u`.  Statement
  unaffected.  Lean: `Papers.OAP.oap43_1` (via `isLUB_mul_right`).
* **OAP 46** (`prop:completelattice`, first.tex:1620, Proposition), proof —
  gap.  The supremum `q` of the increasing idempotents `q_n` is taken in `M`
  (by ω-completeness of `M`), but to be the supremum of `A` *in `P(M)`* it
  must itself be idempotent, which the proof does not show.  Repair: each
  idempotent `q_n ≤ q` lies below the floor `⌊q⌋` (Proposition 35: the
  greatest idempotent below `q`), so `q ≤ ⌊q⌋ ≤ q` and `q = ⌊q⌋` is
  idempotent.  Statement unaffected.  Lean: `Papers.OAP.oap46` (via
  `idem_of_isLUB`).
* **OAP 60** (`lem:completenessousemod`, first.tex:2213, Lemma), proof — slip
  and gap.  With `-n·1 ≤ a, b ≤ n·1` the set `{(1/n)(s - a) ; s ∈ S'}` lies in
  `[0,2]_V`, not in `[0,1]_V` ("clearly … ⊆ [0,1]_V"); use `1/(2n)`.  Second,
  the supremum it has is a supremum *in `[0,1]_V`*, while "so does `S'`, as
  `v ↦ nv + a` is an order isomorphism" needs one *in `V`*: an upper bound of
  `S'` need not lie in the image interval.  Repair: for an upper bound `w`
  choose `N' ≥ n` with `w ∈ [-N'·1, N'·1]`; the supremum relative to that
  interval is below `n·1` and above `a`, so it lies in `[-n·1, n·1]`, hence is
  above the supremum relative to `[-n·1, n·1]`, and it is below `w`.  Statement
  unaffected.  Lean: `Papers.OAP.oap60_directed`, `Papers.OAP.oap60_omega`
  (via `exists_isLUB_of_symIcc`).
* **OAP 66** (`thm:convexextremallydisconnected`, first.tex:2489, Theorem),
  proof — inequalities reversed.  The print has "`f ∗ (g ∨ h) ≤ (f∗g) ∨ (f∗h)`
  and `f ∗ (g ∧ h) ≥ (f∗g) ∧ (f∗h)`"; what monotonicity of `∗` gives, and
  what the next step `d(f∗g, f∗h) ≤ f ∗ d(g,h)` needs, is the reverse:
  `(f∗g) ∨ (f∗h) ≤ f ∗ (g ∨ h)` and `f ∗ (g ∧ h) ≤ (f∗g) ∧ (f∗h)`.  Statement
  unaffected.  Lean: `Papers.OAP.IsUnitRep.dist_mul`.

## EJA — *Pure Maps between Euclidean Jordan Algebras* (arXiv:1805.11496, `1805.11496/main.tex`)

* **EJA 9.4** (`prop:quadraticrep`, main.tex:323, Proposition, item 4) —
  **false as printed.**  The print claims `Q_a b = 0 ⟺ Q_b a = 0 ⟺ a * b = 0`
  "for any EJA `E` and `a, b, c ∈ E`".  In the spin factor `ℝ² ⊕ ℝ`
  (`≅ M₂(ℝ)^sa`) the idempotent `a = (e₁/2, 1/2)` and `b = (e₂, 0)` have
  `Q_a b = 0` but `a * b = (e₂/2, 0) ≠ 0` and `Q_b a = (−e₁/2, 1/2) ≠ 0`
  (in matrices: `a = diag(1,0)`, `b` the flip).  Repair: "for positive
  `a, b`" — the hypothesis of the cited Alfsen–Shultz Lemma 1.26 and the only
  case the paper uses (proof of Prop 11).  Lean:
  `Papers.EJA.quadraticrep_4_false` (refutation),
  `Papers.EJA.eja_Q_eq_zero_iff_mul_eq_zero` (repaired claim).

### EJA 38 (Lemma, main.tex ~855–870) — false as printed (confirmed by independent review, 2026-09-26)

The conclusion `Θ(√f(1)) = √f(1)` fails.  Counterexample: `E = ℝ ⊕ ℝ`,
`q = (a, b)` with `0 < a ≠ b ≤ 1`, `Θ` the swap, `f = Q_q ∘ Θ`, i.e.
`f(x, y) = (a²y, b²x)`: `f` is pure, faithful and ⋄-self-adjoint
(`f^⋄ = f_⋄ =` swap), `√f(1) = (a, b)` is invertible so `Θ` must be the swap,
and `Θ(√f(1)) = (b, a) ≠ (a, b)`.  The broken step is the "uniqueness of
decompositions" (main.tex ~865–868): it matches eigenvalue *sets* and then
identifies the spectral projections of `q²` and `Θ(q²)` index by index.
Candidate repair (38′, sketched, *not yet reviewed*): conclude that
`Θ(√f(1))` operator-commutes with `√f(1)`, and `Θ² = id`.  Points 34, 39, 40
lose their proof but are not refuted (the example satisfies 39:
`f² = Q_{(ab,ab)}`); under 38′ they follow with `Q_q Q_{Θq} = Q_{q·Θq}`.
Review: `lean/docs/research/review-eja38.md`.

*Update 2026-09-26.* The repair 38′ survived a second break-it review and is
proved in Lean: under the hypotheses of 38, `f = Q_q ∘ Θ` with `q = √f(1)`,
`Θ` a unital Jordan isomorphism with `Θ ∘ Θ = id`, and `q`, `Θ(q)` diagonal in
one Jordan frame (so they operator-commute).  The printed `Θ = Θ⁻¹` is true
but its printed proof uses the false `Θ(q) = q` (via `Θ Q_q = Q_q Θ`); the new
proof compares `Q_{Θq} Θ²` with `Q_q` on idempotents.  **EJA 39**'s printed
proof concludes `g = Q_{q²}`, which is wrong in the example (`g = f∘f =
Q_{(ab,ab)}`); the correct computation is `g = Q_q Q_{Θq} Θ² = Q_{q·Θq}`, and
the statement `g = Q_{√g(1)}` stands.  (39's proof also uses that the
⋄-self-adjoint root `f` of `g` is pure, which Def 32 does not require.)  Lean:
`Papers.EJA.eja38_false_as_printed` (refutation), `Papers.EJA.eja38'`
(repaired claim), `Papers.EJA.eja39` (39, root assumed pure).

## REC — *A computer scientist's reconstruction of quantum theory* (arXiv:2109.10707, `2109.10707/short.tex`)

* **REC 7** (`ex:orthomodularlattice`, short.tex:374, Example) — **false as
  printed**, the same slip as OAP 2 (the example is copied from there).  The
  print makes an orthomodular lattice an effect algebra with
  `x ⊥ y ⟺ x ∧ y = 0` and `x ⊻ y = x ∨ y`; in `MO2` both `a ⊻ a^⊥ = 1` and
  `a ⊻ b = 1` with `b ≠ a^⊥`, so orthosupplements are not unique.  Repair:
  `x ⊥ y ⟺ x ≤ y^⊥`; the two agree in a Boolean algebra, the only case used
  later (REC 16).  Lean: `Papers.REC.rec7_as_printed_false` (refutation),
  `Papers.REC.rec7_corrected` (repaired claim, with the order clause).
* **REC 63** (`lem:imageofcomposedmaps`, short.tex:1090, Lemma), proof, first
  sentence — typo: it concludes "hence `im f ≤ im(f∘g)`"; the computation shows
  `im(f∘g) ≤ im f`, as the statement says.  Lean: `Papers.REC.rec63`.
* **REC 69** (`prop:galois-properties`, short.tex:1194, Proposition) — three
  slips: `SEff` is undefined (meant `SPred`); item g) writes `(f∘g)^⋄` for
  `f : A → B`, `g : B → C`, where only `g∘f` is defined (the composable reading
  is meant); the proof of c) exchanges `p` and `q` in its middle step
  (`f_⋄(q) ≤ p ⟺ f^⋄(p^⊥) ≤ q^⊥`, hence `q ≤ f^⋄(p^⊥)^⊥ = f^□(p)`).
  Statements unaffected.  Lean: `Papers.REC.rec69_c`, `Papers.REC.rec69_g`.
* **REC 80** (short.tex:1369, Lemma), second item — gap in the proof: the item
  is stated for arbitrary comprehensions, but the proof takes comprehensions of
  *sharp* predicates, since compatibility (REC 74) provides filters only for
  those.  Repair: `π_p` is also a comprehension for the sharp predicate
  `⌊p⌋ = im π_p` (proof of REC 66 b), so the proof applies with `⌊p⌋` for `p`;
  `q` need not be sharp.  Lean: `Papers.REC.rec80_comprehensions` (printed
  generality).
* **REC 44** (`def:JB-algebra`, short.tex:861, Definition) — the product is only
  required to be a "binary operation"; a JB-algebra (Hanche-Olsen–Størmer 3.1.6,
  which the point cites) is a Jordan *algebra*, so the product must be bilinear.
  Lean: `Papers.REC.JBAlgebra` adds `add_mul`, `smul_mul`.

## SEA — *The three types of normal sequential effect algebras* (arXiv:2004.12749, `2004.12749/second.tex`)

* **SEA 3** (`ex:orthomodularlattice`, second.tex:258, Example), the
  parenthetical "(or more generally, an orthomodular poset)" — **false as
  printed**, the same slip as OAP 2 (the example is copied from there): with
  `x ⊥ y ⟺ x ∧ y = 0` and `x ⋁ y = x ∨ y`, in `MO2` both `a ⋁ a^⊥ = 1` and
  `a ⋁ b = 1` with `b ≠ a^⊥`, so complements are not unique.  Repair:
  `x ⊥ y ⟺ x ≤ y^⊥`; the two agree in a Boolean algebra, the only case used
  later.  Lean: `Papers.SEA.sea3_orthomodular_false_as_printed` (refutation),
  `Papers.SEA.sea3_orthomodular_repaired`.
* **SEA 13** (second.tex:374, Example) — the gloss of "bounded-directed
  complete" reads "every bounded set of self-adjoint elements has a least
  upper bound", dropping *directed*: that is lattice completeness, which fails
  for `B(H)` (Kadison's anti-lattice theorem), contradicting "and include all
  von Neumann algebras" in the next sentence.  Repair: "every bounded
  *directed* set".  Lean: `Papers.SEA.sea13_directedComplete_iff`.
* **SEA 17** (`prop:SEAbasicproperties`, second.tex:490, Proposition), proof —
  three slips, statement unaffected: in the cycle for item 5, "`a ∘ p = a ⇒
  p ∘ a = 0`" should read "`⇒ p ∘ a = a`"; in item 7, `⇒`, the computation
  ends "`= p ∘ a`" for "`= p ⊻ a`"; in item 7, `⇐`, "`p^⊥` and `(p ⊻ a)^⊥`
  are summable idempotents … `a^⊥ = p^⊥ ⊻ (p ⊻ a)^⊥`" should read "`p` and
  `(p ⊻ a)^⊥` … `a^⊥ = p ⊻ (p ⊻ a)^⊥`" (`p^⊥ ⊥ (p ⊻ a)^⊥` fails already for
  `p = 0`, `a ≠ 1`).  Lean: `Papers.SEA.sea17_5`, `Papers.SEA.sea17_7`.
* **SEA 38** (`ex:effect-monoids`, second.tex:970, Example) — "this makes
  `R` into an ordered vector space" needs the positive cone of `V` to be
  *generating* (`V = V₊ - V₊`): otherwise `f ≤ g ≤ f` only says `f = g` on
  `V₊`.  For `V = ℝ` ordered discretely (cone `{0}`), `0 ≤ id ≤ 0` but
  `0 ≠ id`, and "`[0,id]_R`" is not an effect algebra.  SEA 39's cone is
  generating, so the example is unaffected.  Lean:
  `Papers.SEA.sea38_not_antisymm_as_printed` (refutation),
  `Papers.SEA.LinEnd.partialOrder` (with `Fact (Generating V)`).
* **SEA 40** (second.tex:996, Remark), and the paragraph after it
  (second.tex:1004) — "having no non-zero infinitesimals is equivalent to the
  order unit semi-norm being a norm" is **false**, and so is "`W` … where its
  order-unit semi-norm is in fact a norm": in SEA 39's `M` there are no
  non-zero infinitesimals, yet `X = (1 -1; -½ 3/2) - (½ 0; 0 ½) ∈ W` is
  non-zero with `-λ id ≤ X ≤ λ id` for all `λ > 0` (any `X` with column sums
  `0` is).  `‖A‖ = |τ(A)|` is right, as a seminorm.  The seminorm is a norm
  iff no non-zero `a ∈ V` (of any sign) has `-λ1 ≤ a ≤ λ1` for all `λ > 0`;
  absence of infinitesimals only excludes positive such `a`.  Lean:
  `Papers.SEA.sea40_equiv_false_as_printed`, `Papers.SEA.sea40_ouNorm`.

## FDS — *The universal property of infinite direct sums in C\*- and W\*-categories* (arXiv:1907.04714, `1907.04714/direct_sums.tex`)

* **FDS 4.5** (direct_sums.tex:504, Remark) — **ill-typed / false as
  printed.**  For a family `(Aᵢ)ᵢ` the terms `fᵢ fⱼ*` of `∑ᵢⱼ Kᵢⱼ fᵢ fⱼ*`
  (`fⱼ* : B → Aⱼ`, `fᵢ : Aᵢ → B`) compose only when `Aᵢ = Aⱼ`; and for a
  positive semidefinite `K` with some `Kⱼⱼ = 0` (e.g. `K = 0`) the "norm"
  `‖∑ᵢⱼ Kᵢⱼ fᵢfⱼ*‖^½` is only a seminorm, so the space is not a Banach space.
  Repair: a constant family `Aᵢ = A` (as in the remark's own example
  `Aᵢ = ℂ`) and `Kⱼⱼ ≠ 0` for all `j`; then completeness does go "the same way
  as Lemma 4.1".  Lean: `Papers.FDS.KSum.kernel_complete`.

### REC 120 — proof under-specified; statement true; local repair (independent review, 2026-09-26)

The proof takes `ω' := asrt_p ∘ ω` and applies Lemma 119, which is stated for
states, to this substate; with `C(X)`-valued scalars it also cannot be
normalised and uses strict inequalities in `C(X)`.  The gap is present for
`[0,1]` scalars too, so it affects Theorem 103 as much as 102.  Repair: take a
*total* state `ω := π_q ∘ σ` for any state `σ` of the comprehension `{A|q}`
(it exists by separation by states, `q ≠ 0`); then `asrt_q ∘ ω = ω`, Lemma 119
applies as printed, and evaluating at any point `t ∈ X` puts every strict
inequality in `ℝ`.  Theorems 102 and 103 stand as printed (up to the cosmetic
fixes listed for 102/103).  Review: `lean/docs/research/review-rec120.md`.
