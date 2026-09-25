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
