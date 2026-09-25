# OAP — formalisation plan

Paper: A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities*, LICS 2020, arXiv:1912.10040
(`../papers/1912.10040/first.tex`).  Point numbers are the paper's global
counter (`../papers/OAP-points.csv`, 73 points; the two unnumbered `theorem*`
of §3 are forward statements of OAP 68 and OAP 69 and get no separate row).

## Global design (all files)

* **Reuse.** `Theses.B.Eff.EffectAlgebra` (Perp-relation style: `Perp a b`
  and a dependent `ovee a b (h : Perp a b)`), `EffectMonoid`,
  `EffectMonoidHom`, `EAHom`, `prodEffectAlgebra`, `booleanEffectMonoid`,
  `orderIntervalEffectAlgebra`, `orthomodularEffectAlgebra`, the 175V basics
  (`eabasics_*`), and for §8 `OrderUnitSpace` (`Theses/B/Eff/OrderUnit.lean`)
  and the Gudder–Pulmannová representation (179III.2, `gmap`, `Vec`) in
  `EffectAlgebras.lean`.
* **Order.** The paper's `≤` on an effect algebra is the algebraic order `≼`
  (174II).  `Basic.lean` registers it as a *scoped* instance
  `Papers.OAP.eaPartialOrder` (priority 100, so a concrete carrier's own
  order wins), so that Mathlib's `IsLUB`/`IsGLB`/`Monotone`/`DirectedOn`
  apply.  Every later file must `open scoped Papers.OAP`.
* **Totalised sum and difference.** `Papers.OAP.oplus a b` (= `ovee a b h`
  when `Perp a b`, junk `0` otherwise) and `Papers.OAP.osub b a` (= `b ⊖ a`
  when `a ≤ b`, junk `0` otherwise), with `ovee`/`ominus` characterisation
  lemmas.  Statements say "`a ⊥ b` and … `oplus a b`", which is the print's
  "`a ⋁ b` exists and …".
* **n-fold sums** `IsNSum n a s` ("`na` exists and equals `s`"), inductive.
* **ω-completeness / directed completeness** are new `Prop` mixins
  `OmegaComplete E`, `DirectedComplete E` over `[EffectAlgebra E]` (the tree
  has none).  The paper's definition of ω-complete ("increasing sequences
  have suprema") is the field; the "equivalently, countable directed sets have
  suprema" clause of OAP 13 is a theorem.
* **Definition differences with the tree** (recorded in the rows):
  OAP 1 — the print takes `1 ≡ 0^⊥` and the zero axiom on the right
  (`x ⊥ 0`, `x ⋁ 0 = x`); the tree has `1` as a field and the zero axiom on
  the left.  Equivalent (both directions proved: `oap1_axioms`,
  `EffectAlgebra.ofPaper`).  OAP 5 — the print's distributivity is
  bi-additivity (one-sided in each argument); the tree's 178II is the
  four-fold law.  Equivalent (`oap5_biadditive`, `EffectMonoid.ofBiadditive`).
  Neither assumes commutativity.
* Files cannot import one another in a session where oleans are not built,
  so each file's shared infrastructure lives in the earliest file and later
  files import it once `Papers.OAP.Basic` has been built (`lake build
  Papers.OAP.Basic` by the lead, never by a worker).

## Files

| file | sections | points |
|---|---|---|
| `Papers/OAP/Basic.lean` | §2 Preliminaries, §3 Overview (nothing), §4 Basic results | OAP 1–26 |
| `Papers/OAP/FloorCeiling.lean` | §5 Floors, ceilings and division | OAP 27–43 |
| `Papers/OAP/Boolean.lean` | §6 Boolean algebras, halves, convexity | OAP 44–50 |
| `Papers/OAP/Embedding.lean` | §7 Embedding theorems | OAP 51–57 |
| `Papers/OAP/OUS.lean` | §8 Order unit spaces | OAP 58–67 |
| `Papers/OAP/Main.lean` | §9 Main theorems | OAP 68–73 |

Cost: S ≤ 50 lines, M 50–250, L 250–800, XL > 800 (Lean lines, own estimate).

## Points

Legend: kind · content · deps (earlier points / tree declarations) · cost · flags.

### §2 Preliminaries — `Basic.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 1 | Def | effect algebra; `≤`, poset with 0/1, `⊥` anti-iso, `x ⊥ y ⇔ x ≤ y^⊥`, `⊖`; morphism preserves `⊥`, order; embedding (order-reflecting) is injective; iso = surjective embedding | tree `EffectAlgebra`, `EAHom`, `eabasics_*`, `exc_eamorphism_*` | M | definition differs cosmetically (see above) |
| 2 | Ex | orthomodular lattice is an EA with `x ⊥ y ⇔ x ∧ y = 0`, `⋁ = ∨`; lattice order = EA order | tree `orthomodularEffectAlgebra` | M | **false as printed**: `x ∧ y = 0` must be `x ≤ y^⊥` (in MO2 two non-orthogonal atoms have `x ∧ y = 0`, `x ∨ y = 1`, `y ≠ x^⊥`, so complements are not unique).  Refute in MO2; prove the repaired version (the tree's) |
| 3 | Ex | `[0,u]_G` is an EA, orders agree; `[0,1]_C` for a C*-algebra | tree `orderIntervalEffectAlgebra`, `effectsEffectAlgebra` | S | "positive element" = `0 ≤ u` (tree ERRATA 175II.2 is about the thesis, not this print) |
| 4 | Rem | an EA is a bounded poset; Kalmbach extension/monad facts | OAP 1 | S | only the first sentence is mathematics of this paper; the rest is cited literature, not formalised |
| 5 | Def | effect monoid (bi-additive `·`); commutative; idempotent; orthogonal; `P(M)` | tree `EffectMonoid`, `emon_mul_ovee`, `emon_ovee_mul` | M | definition differs (bi-additive vs four-fold), equivalent |
| 6 | Ex | Boolean algebra is a commutative EM under `∧`; conversely an OML where `∧` distributes over `⋁` is Boolean | tree `booleanEffectMonoid`; OAP 2 | M | converse: proof ours (not printed): every pair commutes, then `b ∨ c = b ⋁ (c ∧ b^⊥)` |
| 7 | Ex | `[0,1]_R` of a partially ordered unital ring is an EM; `[0,1]_{C(X)}` commutative | OAP 5 (`ofBiadditive`) | M | real-valued `C(X,ℝ)` for the print's self-adjoint part of complex `C(X)` |
| 8 | Def | EM morphism, embedding, iso = surjective embedding | tree `EffectMonoidHom`; OAP 1 | S | |
| 9 | Ex | Boolean algebra `B` embeds into `[0,1]_{C(X_B)}` (Stone) | OAP 6, 7, 8; Mathlib `DistribLattice.prime_ideal_of_disjoint_filter_ideal` | L | `X_B` = Boolean homs `B → Bool` with the product topology (compact Hausdorff), not a named Stone space |
| 10 | Rem | physical interpretation of `[0,1]_{C(X)}` | — | — | no mathematical content; row only |
| 11 | Ex | direct sum `E₁ ⊕ E₂` of EAs/EMs | tree `prodEffectAlgebra`; OAP 5 | S | |
| 12 | Ex | corner `pM` of an idempotent is an EM with `(pa)^⊥ = p a^⊥`; `Mp = pM` | OAP 19, 20, 23 | M | forward use of §4 lemmas (the print defers "later we will see") |
| 13 | Def | directed set; directed complete; ω-complete; "equivalently" countable-directed ⇔ increasing sequences | — | M | the equivalence is a claim, proved |
| 14 | Rem | dcpo; directed completeness ⇔ filtered infima (via `⊥`) | OAP 1, 13 | S | |
| 15 | Ex | ω-complete BA is an ω-complete EM; complete BA is a directed-complete EM | OAP 6, 13 | S | |
| 16 | Ex | `X` extremally disconnected ⇒ `[0,1]_{C(X)}` directed complete; basically disconnected ⇒ ω-complete | OAP 7, 13; Mathlib `ExtremallyDisconnected`, `continuous_tsum` | L | proof not printed (cites Gillman–Jerison 3N.5); "basically disconnected" defined here |

### §4 Basic results — `Basic.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 17 | Lem | `a·a^⊥ = a^⊥·a` | tree `emon_mul_orth_comm` (same proof) | S | |
| 18 | Lem | `p` idempotent ⇔ `p·p^⊥ = 0` | tree `emon_split_right` | S | |
| 19 | Lem | `p² = p` ⇒ (`pa = a` ⇔ `ap = a` ⇔ `a ≤ p`) | 18 | S | |
| 20 | Lem | idempotents are central | 19 | S | |
| 21 | Cor | `e ↦ (pe, p^⊥e)` is an iso `M ≅ pM ⊕ p^⊥M` | 11, 12, 19, 20, 23 | M | no proof printed |
| 22 | Lem | forcing: `a ≤ b`, `a' ≤ b'`, `b ⋁ b' ≤ a ⋁ a'` ⇒ `a = b`, `a' = b'` | OAP 1 | S | proof typo "Since `a≤a'` and `b≤b'`" for `a≤b`, `a'≤b'` |
| 23 | Lem | `a, b ≤ p` idempotent, `a ⊥ b` ⇒ `a ⋁ b ≤ p` | 19 | S | |
| 24 | Lem | six sup/inf laws for `x ⋁ (·)` and `(·) ⊖ x`, `x ⊖ (·)` on intervals | OAP 1 | M | **clause 3 false as printed** (premise `⋀_s s ⊖ x` should be `⋁_s s ⊖ x`); refuted by the tree's Wright triangle with `x = 0`; the corrected clause is proved |
| 25 | Lem | `a·a^⊥ ⊥ a·a^⊥` | 17 | S | |
| 26 | Lem | ω-complete EM: (1) all `na` exist ⇒ `a = 0`; (2) `a² = 0` ⇒ `a = 0`; (3) `a ⊥ a` ⇒ `⋀ aⁿ = 0` | 24, 25 | M | (3): existence of `⋀ aⁿ` is implicit (decreasing sequence, OAP 13 dual) |

### §5 Floors, ceilings, division — `FloorCeiling.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 27 | Def | infinite sums `⋁_{i∈I} xᵢ` as sup of finite partial sums | 1 | M | |
| 28 | Lem | `(a^N)^⊥ = a^⊥ ⋁ a^⊥a ⋁ … ⋁ a^⊥a^{N-1}` | 5 | S | |
| 29 | Cor | `⋁ₙ a^⊥aⁿ` exists (ω-complete) | 13, 27, 28 | S | |
| 30 | Def | ceiling `⌈a⌉ = ⋁ₙ a(a^⊥)ⁿ`, floor `⌊a⌋ = ⋀ₙ aⁿ` | 17, 29, 35 | S | |
| 31 | Lem | `⋀ₙ a^⊥aⁿ = 0` | 17, 26 | S | |
| 32 | Lem | `⌊a⌋ = ⌊a⌋a = a⌊a⌋` | 17, 31 | M | |
| 33 | Lem | `a·bₙ = 0` ∀n ⇒ `a·⋁bₙ = 0` | 27 | M | |
| 34 | Prop | `ab = 0` ⇒ `a⌈b⌉ = 0` | 18, 28, 32, 33 | M | |
| 35 | Prop | `⌊a⌋` greatest idempotent below `a`; `⌈a⌉` least above; `⌈a⌉^⊥ = ⌊a^⊥⌋` | 28, 32, 34 | M | |
| 36 | Lem | `⌈a ⋁ b⌉ = ⌈a⌉ ∨ ⌈b⌉` | 23 | M | |
| 37 | Thm | `a ∧ b = ⋁ aₙbₙ` (recursive); `M` is a lattice | 19, 20, 26, 34 | L | |
| 38 | Cor | sup/inf in `M` ⇔ in `[a,b]` for non-empty `S ⊆ [a,b]` | 37 | M | |
| 39 | Cor | `a ⋁ (·)` preserves and reflects sup/inf (non-empty S) | 24, 38 | M | |
| 40 | Def | division `a/b = ⋁ₙ a(b^⊥)ⁿ` for `a ≤ b` | 30 | S | |
| 41 | Lem | six division laws; `Mb = [0,b]`; order isos `M⌈b⌉ → Mb` | 17, 19, 22 | L | |
| 42 | Rem | ω-complete EMs are effect divisoids; converse false | 41 | S–M | converse cites Cho's thesis; the "not converse" claim needs a non-commutative divisoid — not formalisable here without importing that construction; record |
| 43 | Thm | multiplication normal: `b(⋁S)b' = ⋁ bSb'`, same for ⋀ | 22, 36, 38, 41 | L | |

### §6 Boolean algebras, halves, convexity — `Boolean.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 44 | Def | Boolean element / Boolean EM | 5 | S | |
| 45 | Prop | `P(M)` is a Boolean algebra; Boolean EM ⇔ Boolean algebra | 19, 20 | M | |
| 46 | Prop | `P(M)` ω-complete when `M` is | 13, 35 | M | |
| 47 | Prop | ω-complete Boolean EM is an ω-complete Boolean algebra | 45, 46 | S | |
| 48 | Def | halvable element / EA | 1 | S | |
| 49 | Def | convex EA (action of `[0,1]`) | 1; tree `EffectModule` over `I` | M | 200-line proof block inside the definition's environment (the construction of the action from a half) belongs to OAP 50 |
| 50 | Prop | halvable ω-complete EM is convex | 24, 26, 43, 49 | XL | dyadic action then ω-limits |

### §7 Embedding theorems — `Embedding.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 51 | Lem | ceiling of a halvable element is halvable | 30, 35 | M | |
| 52 | Prop | maximal orthogonal family of non-zero idempotents, each halvable or Boolean | 18, 25, 51; Zorn | M | |
| 53 | Prop | `a ↦ (ae)ₑ : M → ∏_{e∈E} Me` is an EM embedding | 20, 43 | M | "⊕" of an infinite family is the product |
| 54 | Thm | ω-complete `M` embeds into `M₁ ⊕ M₂`, `M₁` convex, `M₂` ω-complete Boolean algebra | 47, 50, 52, 53 | M | |
| 55 | Ex | ω-complete EM with no maximal halvable idempotent, so not `M₁ ⊕ M₂` | 7, 48 | L | "straightforward to check" — unverified; high risk |
| 56 | Lem | directed-complete: maximal self-summable `a`; `a ⋁ a` idempotent; everything below `(a ⋁ a)^⊥` idempotent | 23, 25, 26 | M | |
| 57 | Thm | directed-complete `M ≅ M₁ ⊕ M₂`, `M₁` convex dc, `M₂` complete BA | 21, 47, 50, 56 | M | |

### §8 Order unit spaces — `OUS.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 58 | Def | OUS, Archimedean | tree `OrderUnitSpace`, `OUSArchimedean` | S | compare definitions |
| 59 | Def | unit interval `[0,1]_V` is a convex EA; ω-/directed-complete OUS | 3, 49 | M | |
| 60 | Lem | OUS directed complete ⇔ bounded directed complete (and ω) | 59 | M | |
| 61 | Lem | bounded ω-complete OUS is Archimedean | 60 | S | |
| 62 | Thm | convex EA ≅ `[0,1]_V` (Gudder–Pulmannová) | tree 179III.2 (`gmap`, `Vec`) | M | reuse; cited |
| 63 | Prop | ω-complete convex EM: multiplication is bilinear | 24, 61, 62 | L | |
| 64 | Thm | Yosida: norm-complete lattice-ordered Archimedean OUS ≅ `C(Φ)` | Mathlib (no Yosida) | XL | cited, not proved in the paper; not in Mathlib — the dominant cost of the whole paper |
| 65 | Rem | Yosida duality (cited) | — | — | row only |
| 66 | Thm | convex ω-complete EM ≅ `[0,1]_{C(X)}`, `X` basically disconnected (ED if dc) | 37, 60–64 | L | "Hausdorff" without "compact" in the statement (proof produces compact `X`) |
| 67 | Rem | Kadison alternative (cited) | — | — | row only |

### §9 Main theorems — `Main.lean`

| OAP | kind | content | deps | cost | flags |
|---|---|---|---|---|---|
| 68 | Thm | ω-complete `M` embeds into `[0,1]_{C(X)} ⊕ B` | 54, 66 | S | |
| 69 | Thm | directed-complete `M ≅ [0,1]_{C(X)} ⊕ B` | 57, 66 | S | |
| 70 | Cor | ω-complete EM is commutative | 68 | S | proof says multiplication of `B` "is given by the join" — meet |
| 71 | Thm | no zero divisors ⇒ `M ≅ {0}`, `{0,1}` or `[0,1]` | 25, 50, 51, 66; Urysohn | M | |
| 72 | Rem | normalised ω-effectus scalars (cited) | — | — | row only |
| 73 | Rem | outlook: ordered rings, open questions | 7, 69 | — | row only |

## Order of work

Basic.lean (this session) → FloorCeiling → Boolean → Embedding → OUS (Yosida
is the long pole; start it in parallel early) → Main.

## Status and handover (2026-09-26)

**`Basic.lean` done**: OAP 1–26 all formalised, 1,845 lines, `scripts/lean1.sh`
exit 0, no `sorry`, no warnings; 72 rows in `docs/audit/papers-oap.csv`.
Two points are false as printed and are refuted in Lean (OAP 2,
OAP 24 clause 3; `../papers/ERRATA.md`).  `Papers.lean` imports it, but
`Papers.OAP.Basic` has **no olean yet**: before `FloorCeiling.lean` can start,
the lead must build it once (`lake build Papers.OAP.Basic`, serialised like
any compile).

Infrastructure the later files should use (all in `namespace Papers.OAP`,
`open scoped Papers.OAP`):

* `a ⋎ b` (`oplus`), `b ⊖ a` (`osub`) and their API: `oplus_eq`,
  `oplus_assoc`, `perp_assoc_left`, `oplus_left_cancel`, `oplus_le_oplus`,
  `oplus_le_oplus_left_iff`, `osub_eq_iff`, `oplus_osub`, `osub_osub`,
  `osub_le_osub_right(_iff)`, `oplus_oplus_comm` (four-term rearrangement),
  `isSumOf_append` (lists ↔ nested sums).
* EM API: `mul_oplus`, `oplus_mul`, `emul_zero`, `ezero_mul`, `emul_le_left/right`,
  `emul_le_emul_left/right`, `emul_oplus_emul_orth`, `emul_oplus_orth_emul`,
  `idem_orth`, `emul_eq_of_le(')`, `emul_orth_eq_zero_of_le`,
  `orth_emul_eq_zero_of_le`, powers `a ^ n` via the scoped `emMonoid`.
* `IsNSum a n s` (`na` exists) with `unique`, `add`, `of_le`, `le_of_le`,
  `emul_right`; `OmegaComplete`, `DirectedComplete`,
  `OmegaComplete.exists_isGLB`, `isGLB_orth_of_isLUB`.
* Constructors: `EffectMonoid.ofBiadditive`, `prodEffectMonoid` (instance),
  `cornerEffectAlgebra/Monoid p hp` (on `leftCorner p`), `EMIsIso`,
  `EMEmbedding`, `oap8_isIso_iff`, `unitIntervalEffectMonoid R`.

Pitfalls met:

* The scoped order has priority 100, so on a **subtype or product** of an
  effect algebra `≤` resolves to Mathlib's subtype/product order, *not* the
  effect-algebra order of the corner/product.  State such lemmas with the
  instance explicit (`prod_le_iff`, `corner_le_iff`) and apply them by term
  (`(prod_le_iff).1 h`), not by `rw`: the instance reached through
  `EffectMonoid.toEffectAlgebra (ofBiadditive …)` is defeq but not syntactically
  equal to the effect algebra it was built from.
* `refine ⟨?_⟩`/`constructor` on `@OmegaComplete X inst` re-synthesises the
  instance; use `letI := inst` first.
* **Never pipe `scripts/lean1.sh` into `head`**: when the reader closes, lean
  blocks forever in a futex wait *while holding the compile lock*
  (2026-09-26: two such hung compiles from sibling sessions had to be
  killed).  Redirect to a file and read the file.

Flags for the later files (from the plan above): OAP 66 omits "compact";
OAP 70's proof says "join" for the meet of `B`; OAP 55's "straightforward to
check" is unverified; OAP 64 (Yosida) is not in Mathlib and is the long pole.
