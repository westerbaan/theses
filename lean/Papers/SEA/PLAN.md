# SEA — formalisation plan

Paper: A. Westerbaan, B. Westerbaan, J. van de Wetering, *The three types of
normal sequential effect algebras*, Quantum 2020 (arXiv:2004.12749), source
`../papers/2004.12749/second.tex`, point index `../papers/SEA-points.csv`
(73 numbered points, one global counter).

Companion paper **OAP** (`Papers/OAP/`, formalised in parallel, *not*
importable while it is being built).  Where SEA cites OAP ("[first]") the
cited result is either proved locally (only when cheap) or taken as an
explicit hypothesis of the SEA declaration — a `Prop` in `Papers/SEA/Basic.lean`
named after the OAP point (`OAP47`, `OAP43`, `SEA35` = OAP 57+69 in the form
SEA prints) — and the audit row says `left-cost`, "waits on OAP n".  The SEA
citations use OAP's own numbering (checked against `OAP-points.csv`): Cor 21,
Thm 43, Prop 47, Lemma 56, Thms 57/69, Thm 71.

## Files

| file | section | points |
|---|---|---|
| `Basic.lean` | §2 preamble, §2.1 SEAs, §2.2 effect monoids (incl. §2.2.1) | 1–37 |
| `Example.lean` | §2.3 an interesting SEA | 38–40 |
| `Boolean.lean` | §3 Boolean SEAs | 41–44 |
| `AlmostConvex.lean` | §4 almost-convex SEAs | 45–60 |
| `PureAConvex.lean` | §5 pure a-convexity | 61–68 |
| `Assoc.lean` | §6 associative sequential products | 69–73 |

Every later file imports `Papers.SEA.Basic` (once it has an olean).

## Reuse of the theses tree, and differences

* effect algebra: `Theses.B.Eff.EffectAlgebra` (175I) — same axioms; order
  `≼` = `PCM.le`, `ominus`, `orth`; the basic facts of SEA 7 are 175V.
* convex action (SEA 8) = `EffectModule I E` (179II over the effect monoid
  `[0,1]`) — the four axioms coincide; Gudder's representation (SEA 9) is
  `effectModule_unitInterval_representation`.
* effect monoid (SEA 29) = `Theses.B.Eff.EffectMonoid` (178II), whose
  distributivity is the thesis's four-term law; bi-additivity is
  `emon_mul_ovee`/`emon_ovee_mul`.
* SEA (SEA 15): the tree's `SequentialEffectAlgebra` (225IV, eff.tex) has a
  **weaker S5**: it asks `c | a ⊙ b` only when `a ⊥ b`.  The paper asks it
  unconditionally.  `Papers.SEA.SEA` therefore *extends* the tree's class
  with the missing field `seq_comm_seq`.  (Not a defect of the tree: it is
  eff.tex's own wording.)  The C*-algebra instance (SEA 16) reuses the
  tree's `sqrtConj` lemmas (`Theses/B/Eff/VNExamples.lean`), whose proof of
  the tree's S5 never used `a ⊥ b` for the product half.
* directed completeness, suprema, normality: new (the tree has none for
  effect algebras), stated with the EA order `≼`.

## Points

Kinds: D definition, R remark, E example, P proposition, L lemma, T theorem,
C corollary.  Cost: 0 = no declaration / wrapper, 1 = short, 2 = moderate,
3 = substantial, H = hypothesis (cited OAP / external result not proved).

| n | kind | content | file | depends on | cost |
|---|---|---|---|---|---|
| 1 | D | effect algebra; ≤ is a poset, `⊥` anti-iso, `a⊥b ⇔ a≤b^⊥`, `⊖` unique | Basic | tree 175I, 175V | 0 |
| 2 | R | terminology "summable" | Basic | — | 0 (no decl) |
| 3 | E | Boolean algebra (orthomodular poset) is an EA, orders agree | Basic | tree 175II.5 | 1 (orthomodular *poset* not done: tree has lattices only) |
| 4 | E | `[0,u]_G` interval EA, orders agree; `[0,1]_C` | Basic | tree 175II.2 | 1 |
| 5 | R | GPT remark | Basic | — | 0 |
| 6 | E | direct sum `E ⊕ F` | Basic | tree 175III | 0 |
| 7 | P | involution, positivity, cancellation, `≤` anti, `⊥ ⇔ ≤ ^⊥` | Basic | tree 175V | 0 |
| 8 | D | convex action / convex EA | Basic | tree 179II | 0 |
| 9 | E | `[0,u]_V` convex; converse (Gudder) | Basic | tree 179III.2 | 0 |
| 10 | R | literature | Basic | — | 0 |
| 11 | D | directed set, directed complete | Basic | — | 1 |
| 12 | E | complete Boolean algebra is directed complete | Basic | 3, 11 | 1 |
| 13 | E | `[0,1]_A` directed complete ⇔ A bounded-directed complete; `C(X)` ⇔ X extremally disconnected | Basic | 11 | 3 (first iff), H (Gillman–Jerison) — **flag** below |
| 14 | R | filtered infima exist in a dcEA | Basic | 11 | 1 |
| 15 | D | SEA (S1–S5), normal (S6), commute, central, centre, idempotent, Boolean, orthogonal | Basic | tree 225IV | 1 |
| 16 | E | `[0,1]_A` is a SEA with `√a b √a`; normal when A monotone complete; JB(W) | Basic | tree VNExamples `sqrtConj` | 1 (SEA), 3 (normal: needs normality of `√a · √a` in monotone-complete A), H (JB) |
| 17 | P | seven basic properties of SEAs | Basic | 15 | 2 |
| 18 | L | `a,b ≤ p` idempotent ⇒ `a ⊕ b ≤ p` | Basic | 17 | 1 |
| 19 | L | `a ⊙ a^⊥` self-summable | Basic | 17 | 1 |
| 20 | L | `a ⊕ ⋁S = ⋁ (a ⊕ s)` | Basic | 11 | 2 |
| 21 | L | only 0 has all n-fold sums in a dcEA | Basic | 20 | 2 |
| 22 | L | normal SEA has no nilpotents | Basic | 19, 21 | 2 |
| 23 | P | left corner `p ⊙ E` is a (normal) SEA | Basic | 17 | 3 |
| 24 | P | central idempotent splits `E ≅ pE ⊕ p^⊥E` | Basic | 23 | 2 |
| 25 | D | Boolean idempotent | Basic | 23 | 0 |
| 26 | D | commutant, bicommutant | Basic | 15 | 0 |
| 27 | R | bicommutant ≠ least commutative subalgebra | Basic | 26 | 0 (no decl; **flag**) |
| 28 | P | `S''` of a commuting `S` is a commutative normal sub-SEA | Basic | 26 | 3 |
| 29 | D | effect monoid; commutative, idempotent, orthogonal, Boolean | Basic | tree 178II | 0 |
| 30 | E | Boolean algebra is Boolean comm. EM; converse | Basic | tree 178III.2; converse **OAP 47** | 1 + H |
| 31 | E | `[0,1]_R` of an ordered unital ring is an EM; `C(X)`; non-commutative EMs; EM with S3 is a SEA | Basic | tree 178III | 2 |
| 32 | E | commutative SEA ⇔ commutative EM; normal ⇔ dc (converse **OAP 43**) | Basic | 31 | 2 + H |
| 33 | R | distributive SEAs (Gudder) | Basic | — | 0 |
| 34 | E | corners `pM`, `M ≅ pM ⊕ p^⊥M` (OAP 20/21, proved locally: cheap) | Basic | 29 | 2 |
| 35 | T | structure theorem for dc EMs (**OAP 57 + 69**) | Basic | — | H |
| 36 | C | spectral theorem: `{a}'' ≅ [0,1]_{C(X)} ⊕ B` | Basic | 28, 32, 35, OAP 47 | 2 given H |
| 37 | C | unique square roots in a normal SEA | Basic | 36 | 2 given H |
| 38 | E | `[0,id]` in `End(V)` is a convex EM | Example | 31 | 2 |
| 39 | E | the 2×2 example is a non-commutative SEA | Example | 38 | 2 (**check the cone**) |
| 40 | R | Archimedean remarks; order-unit norm = `|τ|` | Example | 39 | 2 (partly unnumbered claims) |
| 41 | L | `a⊙b` idempotent ⇒ `a⊙b ≤ b`; both idempotent ⇒ commute | Boolean | 17 | 1 |
| 42 | C | Boolean idempotent is central | Boolean | 41 | 1 |
| 43 | P | `p⊙q` idempotent ⇔ `p|q`, then `p⊙q = p∧q` | Boolean | 41 | 1 |
| 44 | P | Boolean SEA is a Boolean algebra, complete if normal | Boolean | 43, **OAP 47** | 2 + H (**flag**) |
| 45 | D | a-convex action | AlmostConvex | 8 | 0 |
| 46 | R | convex = a-convex + additivity | AlmostConvex | 45 | 0 |
| 47 | D | horizontal sum | AlmostConvex | — | 2 |
| 48 | E | `HS([0,1],[0,1])` normal SEA, two a-convex actions, not convex | AlmostConvex | 47 | 3 |
| 49 | D | floor `⌊a⌋ = ⋀ aⁿ` | AlmostConvex | 14 | 1 |
| 50 | L | `⌊a⌋` largest idempotent below a | AlmostConvex | 49 | 2 |
| 51 | L | unique division when `⌊a⌋=0` | AlmostConvex | 36 (**OAP 69**) | 3 given H |
| 52 | P | additive `[0,1] → E` normal, commuting, floor 0, determined by one value | AlmostConvex | 21, 51 | 3 |
| 53 | D | half | AlmostConvex | — | 0 |
| 54 | P | a half is central iff unique | AlmostConvex | 17 | 1 |
| 55 | P | a-convex action from unital additive φ | AlmostConvex | 52 | 2 |
| 56 | E | a-convex action not determined by scalars | AlmostConvex | 47, 48 | 3 |
| 57 | T | seven equivalent characterisations of convexity | AlmostConvex | 52–55, **OAP 69** (`{h}''` with a half) | 3 given H |
| 58 | T | maximal a-convex idempotent is central with Boolean complement | AlmostConvex | 22, 42, 55, cf. **OAP 56** | 3 |
| 59 | T | `E ≅ E₁ ⊕ E₂`, a-convex ⊕ complete Boolean | AlmostConvex | 24, 44, 58 | 1 |
| 60 | C | finite SEA is a Boolean algebra | AlmostConvex | 59 | 2 |
| 61 | D | purely a-convex, a-convex factor | PureAConvex | 45 | 0 |
| 62 | P | a-convex = convex ⊕ purely a-convex | PureAConvex | 57, **OAP 69** | 2 given H |
| 63 | C | purely a-convex ⇔ no convex central corner | PureAConvex | 62 | 1 |
| 64 | T | main theorem `E ≅ B ⊕ E_c ⊕ E_ac` | PureAConvex | 59, 62 | 1 |
| 65 | P | a-convex normal SEA is a union of convex sub-SEAs | PureAConvex | 28, 57 | 2 given H |
| 66 | D | commuting halves | PureAConvex | — | 0 |
| 67 | P | a-convex normal: convex ⇔ commuting halves | PureAConvex | 57 | 1 |
| 68 | T | commuting halves ⇒ `E = B ⊕ E_c` | PureAConvex | 64, 67 | 1 |
| 69 | P | associative ⇒ idempotents central | Assoc | 17 | 1 |
| 70 | P | associative + commuting halves ⇒ commutative | Assoc | 36, 57, 68 | 3 given H |
| 71 | L | `a⊙b = a ⇒ a⊙⌊b⌋ = a` | Assoc | 50 | 1 (**flag**) |
| 72 | L | only trivial idempotents ⇒ no zero divisors | Assoc | 71 | 1 |
| 73 | P | associative normal a-convex factor ≅ horizontal sum of `[0,1]`'s | Assoc | 47, 52, **OAP 71** | 3 given H |

## Status

* `Basic.lean` (2026-09-26): points 1–37 all done — 32 with declarations, 5
  remarks without (2, 5, 10, 27, 33); compiles exit 0, no `sorry`,
  axiom-clean; 2,720 lines (the C*-algebra examples SEA 13/16, ~470 lines at
  the end, can move to their own `CStar.lean` once `Basic` has an olean).
  Hypotheses in use: `SEA35` (OAP 57+69), `OAP47`, `OAP43`.  Not formalised:
  SEA 13's second claim (C(X), Gillman–Jerison), SEA 16's monotone-complete
  and JB(W) cases.  ERRATA filed: SEA 3, 13, 17.

## Flags (to check when the point is reached; ERRATA only if a reader would stumble)

* **3** (found in phase 1): the parenthetical "orthomodular poset" is false
  as printed, same slip as OAP 2 (ERRATA SEA 3).
* **17** (found in phase 1): three slips in the proof (ERRATA SEA 17).

* **13**: "bounded-directed complete, that is: if every bounded set of
  self-adjoint elements has a least upper bound" drops *directed*: as printed
  it is lattice-completeness, which fails for `B(H)` (Kadison's anti-lattice
  theorem), contradicting "and include all von Neumann algebras".
* **16**: the normal half ("if A is bounded-directed complete then `[0,1]_A`
  is a normal SEA") needs `x ↦ √a x √a` to preserve directed suprema and
  commutation with `⋁S`; no argument or citation is printed.
* **27**: `{0} × [0,1]` is called a "commutative subalgebra" of `[0,1]²` but
  does not contain `1`; it is a corner, not a sub-SEA.  Remark, no decl.
* **31**: "(partially) ordered unital ring" needs `0 ≤ 1` for `[0,1]_R` to be
  non-empty (same defect as thesis B 175II.2); Mathlib's `IsOrderedRing` has it.
* **39**: the cone "`(a,b) > 0` iff `a + b > 0`" is not closed and not
  generating in the usual sense; the membership criterion for `M` must be
  re-derived before transcribing.
* **44**: the proof cites OAP 47, which is about *ω-complete* Boolean effect
  monoids, for an arbitrary Boolean SEA; the non-normal case needs the
  completeness-free argument (Boolean EM ⇒ Boolean algebra).
* **71**: the proof writes `a ⊙ b^4 = 0`, `a ⊙ b^{2^n} = 0`, `a ⊙ bⁿ = 0`
  where it means `= a` throughout, and "since `bⁿ ≤ b^{2^n}`" is reversed
  (powers decrease; the argument needs `b^{2^n} ≤ bⁿ`, then
  `a = a ⊙ b^{2^n} ≤ a ⊙ bⁿ ≤ a`).  The conclusion is right.
