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

### `FloorCeiling.lean` done (2026-09-26)

OAP 27–43 all formalised, 1,285 lines, `scripts/lean1.sh` exit 0, no
`sorry`, no warnings; 31 rows in `docs/audit/papers-oap.csv`.  Nothing false
as printed.  One proof gap filed in `../papers/ERRATA.md` (OAP 43: the printed
chain uses `⋁_s b·s` before its existence is shown; repaired with the meet of
OAP 37).  OAP 42: only the first claim (ω-complete EM ⇒ effect divisoid, the
tree's `EffectDivisoid`) is formalised; the converse is cited.
`FloorCeiling.lean` imports `Theses.B.Eff.StatesPredicates` (for
`EffectDivisoid`; a 14 MB olean).  **The lead must build
`Papers.OAP.FloorCeiling` before `Boolean.lean` can import it.**

Infrastructure for §6 and later (namespace `Papers.OAP`):

* Sums: `HasOSum` (OAP 27, any index type), `psum x N`, `SeqSummable x`,
  `HasSeqSum x s`, `seqSum x`, `oap27_nat` (the two agree on `ℕ`),
  `exists_hasSeqSum`, `psum_le_psum` (termwise domination), `HasSeqSum.mono`,
  `HasSeqSum.oplus`, `isLUB_oplus_of_monotone` (sups of increasing sequences
  add), `psum_mul_left/right`, `isNSum_of_le_psum`,
  `eq_zero_of_le_seqSummable` (a common lower bound of a summable sequence is
  `0`: OAP 26.1).
* Ceilings/floors (`[OmegaComplete M]`): `ceil`, `floor`, `ceil_idem`,
  `le_ceil`, `ceil_le` (least idempotent above), `ceil_mono`, `ceil_of_idem`,
  `floor_idem`, `floor_le`, `le_floor`, `floor_of_idem`,
  `ceil_eq_orth_floor`, `oap35_3` (duality), `oap34` (`ab = 0 ⇒ a⌈b⌉ = 0`),
  `pow_orth_comm`, `mul_orth_pow_comm`, `eq_one_of_le_of_orth_le`.
* Lattice: `emInf`, `emSup = (a^⊥ ∧ b^⊥)^⊥`, `isGLB_emInf`, `isLUB_emSup`,
  `emInf_le_left/right`, `le_emInf`, `le_emSup_left/right`, `emSup_le`;
  `emLattice M` is a `Lattice M` **def** (built on `eaPartialOrder`, so its
  `≤` is the scoped one) — not an instance.
* Intervals: `oap38_sup/inf` (sup/inf in `Set.Icc a b` with the subtype order
  ⇔ in `M`), `oap39_1/2` (`a ⋎ ·` preserves and reflects sup/inf).
* Division: `odiv a b` (= `a/b`), `oap41_1..6`, `odiv_mono`, `odiv_le_ceil`,
  `le_odiv_mul`, `mulRightIso b`, `mulLeftIso b : Set.Iic (ceil b) ≃o
  Set.Iic b`, the mirror division `ldiv b a` (= `b\a`) with `mul_ldiv`,
  `ldiv_mul`, `ldiv_self`.
* Normality (OAP 43): `isLUB_mul_right/left`, `isGLB_mul_right/left`
  (non-empty `S`), `oap43_1/2` for `b·S·b'`.
* **Opposite effect monoid** `EMOp M` (type synonym; `EffectMonoid` and
  `OmegaComplete` instances, reversed product).  Its order, sums and
  complements are `M`'s by definition, so the mirror image of a lemma is
  `foo (M := EMOp M) …` used at type `M` (works by `exact`, defeq); for
  `ceil` use `ceil_op` (propositional).  This is how every left/right pair in
  §5 is obtained; §6–7 can do the same.

Pitfalls met:

* On a type synonym give **only** the `EffectMonoid` instance (build the
  effect algebra inside with `letI`): a separate `EffectAlgebra (EMOp M)`
  instance makes `OmegaComplete (EMOp M)` unfindable, because the two
  instance paths agree only after unfolding `EffectMonoid.ofBiadditive`
  (not reducible).
* `obtain ⟨y, hy, -⟩ := y'` on a subtype element silently clears every
  hypothesis mentioning `y'`; name the component instead of `-`.
* `rw [← e]` with `e : … = a` rewrites *every* `a`, including the arguments
  of `infSeq a b`; use `show` + `exact` or `le_of_le_of_eq`.

Hints for `Boolean.lean` (OAP 44–50): OAP 45's `p·q = p ∧ q` is
`isGLB_emInf` plus `emul_eq_of_le`; complements in `P(M)` are `orth`
(`idem_orth`).  OAP 46 (`P(M)` ω-complete) will want `ceil`/`floor` and
their extremal properties (`ceil_le`, `le_floor`); derive the route from the
print's own proof, not from this note.  OAP 50 uses OAP 24 (Basic), OAP 26 (Basic) and OAP 43 (`isLUB_mul_left/right`,
`oap43_1`).

### `Boolean.lean` done (2026-09-26)

OAP 44–50 all formalised, 850 lines, `scripts/lean1.sh` exit 0, no `sorry`,
no warnings; 12 rows in `docs/audit/papers-oap.csv`.  Nothing false as
printed.  One proof gap filed in `../papers/ERRATA.md` (OAP 46: the supremum
in `M` of the idempotents `q_n` is never shown to be idempotent; repaired with
the floor of OAP 35, `idem_of_isLUB`).  `Papers.lean` imports it.  **The lead
must build `Papers.OAP.Boolean` before `Embedding.lean` can import it.**

Infrastructure for §7 and later (namespace `Papers.OAP`):

* Boolean (OAP 44): `IsBooleanElem a` (`∀ b ≤ a, b*b = b`), `IsBooleanEM M`
  (`IsBooleanElem 1`), `isBooleanEM_iff` (every element idempotent).
* Idempotents, no completeness needed: `idem_mul`, `isGLB_idem` (`p·q` is
  the meet in `M`), `isLUB_idem` (`(p^⊥q^⊥)^⊥` is the join in `M`),
  `orth_orth_mul_orth` (`(p^⊥q^⊥)^⊥ = p ⋎ p^⊥q`, any `p`, `q`),
  `perp_idem_iff` (`p ⊥ q ⟺ pq = 0` for idempotent `q`), `oplus_idem_eq`
  (orthogonal idempotents: `p ⋎ q = p ∨ q`), `mul_orth_mul_idem`.
  With ω-completeness: `idem_of_isLUB` (sup of idempotents is idempotent).
* `P(M)` (OAP 45): `idemBooleanAlgebra M : BooleanAlgebra (idempotents M)`,
  a **scoped** instance (order = subtype order of `M`'s, so `idem_le_iff` is
  `Iff.rfl`; `⊓` is `*`, `ᶜ` is `orth`, all by `rfl`: `oap45_inf/sup/compl`).
  As an effect monoid `P(M)` is `booleanEffectMonoid (idempotents M)` —
  always written `@… (booleanEffectMonoid _)`, never as an instance.
  `idemIncl M` (inclusion, an EM morphism), `booleanIso hM : M → P(M)` for
  Boolean `M`, `oap45_isIso`, `oap45_iff` (Boolean ⟺ `EMIsIso` to some
  Boolean algebra's EM).
* ω-completeness (OAP 46–47): `oap46` (countable `A ⊆ P(M)` has a sup in
  `P(M)` which is also the sup in `M`), `oap46_omegaComplete`
  (`@OmegaComplete (idempotents M) (booleanEffectAlgebra _)`, the OAP 15
  form), `oap47` (the three together for Boolean `M`).  For OAP 54 "`M₂` an
  ω-complete Boolean algebra" these are the forms available.
* Halves and convexity (OAP 48–49): `IsHalvable a` (`∃ b, Perp b b ∧ b ⋎ b
  = a`), `HalvableEA E`; `ConvexAction E` (structure: `act : I → E → E` and
  the four axioms; the `λ+μ` axiom is stated for every `ν : I` with
  `(ν:ℝ) = λ + μ`), `IsConvex E := Nonempty (ConvexAction E)`;
  `ConvexAction.toEffectModule` / `.ofEffectModule`, `oap49_iff` (convex ⟺
  the tree's `EffectModule I E` over `unitInterval.effectMonoid`) — use this
  for §8's Gudder–Pulmannová (tree 179III.2).
* OAP 50: `IsHalf a := Perp a a ∧ a ⋎ a = 1`; `IsHalf.convexAction h`, with
  `act l x = dyCl a l * x` (`convexAction_act`, `rfl`); `dyEl a n m` (`= m·aⁿ`,
  the dyadic element), `dyCl a r` (`\overline{r}`: sup of the `dyEl` with value
  `< r`, and `0`); `dyCl_dyEl`, `dyCl_one`, `dyCl_add`, `dyCl_mul`
  (`\overline{λ}·\overline{μ} = \overline{λμ}`), `dyEl_shift/pair/mul/le`.
  So `λ(a·b) = (λa)·b` holds by `emul_assoc`; `a·(λb) = λ(a·b)` does **not**
  follow from anything here (that is OAP 63's business: `dyCl` need not be
  visibly central).
* General tools: `nsum x m` (total `m`-fold sum) with `IsNSum.eq_nsum`,
  `IsNSum.split` (`(m+k)x` exists ⇒ `mx ⊥ kx`, sum), `IsNSum.comp`
  (`k·x = y`, `m·y = s` ⇒ `(km)·x = s`), `IsNSum.emul_left`;
  `isLUB_image2_oplus` (sup of pairwise sums of two sets), `isLUB_image2_mul`
  (`(⋁S)(⋁T) = ⋁ st`, OAP 43 twice), `isLUB_of_cofinal`, and an
  Archimedean principle `le_of_osub_le` (`eₖ ≤ x`, `⋀eₖ = 0`, `x ⊖ eₖ ≤ u`
  ⇒ `x ≤ u`, via the meet of OAP 37); real-side `dyadic_approx`,
  `exists_inv_two_pow_lt`, `dy_nat_le`, `dy_val_pair`, `dy_val_mul`.

Notes for `Embedding.lean` (OAP 51–57), from reading §7 against what exists
(re-derive the routes from the print, not from this note):

* Corners: Basic's `cornerEffectMonoid p hp` lives on `leftCorner p` with the
  *subtype* order problem of Basic's pitfalls (use `corner_le_iff`).  OAP 54
  needs `OmegaComplete` of a corner `pM` (for OAP 50 on `M₁`, OAP 47 on `M₂`)
  — not yet proved anywhere; sups of increasing sequences below `p` are the
  sups in `M` (they stay `≤ p`), so it is short, but mind the instance path
  (`letI` the corner EM first; see Basic's pitfall on `refine ⟨?_⟩`).  Also
  `HalvableEA` of the corner from `IsHalvable p` in `M` (the half `b ≤ p` is
  in the corner) and `IsBooleanEM` of the corner from `IsBooleanElem p`.
* OAP 53 needs an effect monoid on an arbitrary product `∀ e : E, Me`; only
  the binary `prodEffectMonoid` exists.  Build it with
  `EffectMonoid.ofBiadditive` as `prodEffectMonoid` does.
* OAP 52 (Zorn over orthogonal families of non-zero idempotents) will want
  `perp_idem_iff` / `oplus_idem_eq` and OAP 25 (`a·a^⊥ ⊥ a·a^⊥`) and OAP 51.
* Pitfall met here: a `letI` whose goal is a `Prop` trips the style linter
  (`haveILetI`); use `let _ := …` inside proofs.

### `OUS.lean` done (2026-09-26)

OAP 58–67 all formalised (OAP 64 is `Yosida.lean`; 65 and 67 are cited
remarks, rows only), 1,222 lines, `scripts/lean1.sh` exit 0, no `sorry`, no
warnings; 20 rows in `docs/audit/papers-oap.csv`.  Imports `Papers.OAP.Basic`,
`Papers.OAP.Yosida`, `Theses.B.Eff.OrderUnit`, `Theses.B.Eff.EffectAlgebras`,
`Mathlib.Topology.UrysohnsLemma` — **not** `FloorCeiling`.  Nothing false as
printed; two proof slips filed in `../papers/ERRATA.md` (OAP 60: `1/n` should
be `1/(2n)`, and a supremum relative to `[0,1]_V` is not yet one in `V`;
OAP 66: the two `∗`-vs-`∨/∧` inequalities are reversed).  OAP 66 is stated
with **compact** `X` (the print omits it) and **waits on OAP 37**: the
hypothesis `oap37 : ∀ a b : M, ∃ c, IsLUB {a, b} c`, discharged in a file
that imports `FloorCeiling` by `fun a b => ⟨emSup a b, isLUB_emSup a b⟩`.

What §9 will use (namespace `Papers.OAP`):

* **`oap66 [EffectMonoid M] [EffectModule I M] [OmegaComplete M] (oap37)`** :
  `∃ X (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
  (f : EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1)), EMIsIso f ∧ (f respects
  `[0,1]`-scalars) ∧ BasicallyDisconnected X ∧ (DirectedComplete M →
  ExtremallyDisconnected X)`, with `X : Type u` in `M`'s universe.  The
  effect monoid on `Set.Icc (0 : C(X, ℝ)) 1` is Basic's
  `unitIntervalEffectMonoid`, used through
  `attribute [local instance] unitIntervalEffectMonoid` (a section-local
  instance; do the same in `Main.lean`, or write the `@`-form).
  "Convex" is the tree's `EffectModule I M` (OAP 49's `Boolean.lean` notion
  should be checked against it before OAP 68 plugs OAP 54's `M₁` in).
* `oap63 [OmegaComplete M] l a b : l • (a * b) = (l • a) * b ∧ l • (a * b) =
  a * (l • b)` (bilinearity).
* OUS side: `ousEA V` / `ousEMod V` (`[0,1]_V`), `OUSOmegaComplete`,
  `OUSDirectedComplete`, `OUSBoundedOmegaComplete`,
  `OUSBoundedDirectedComplete`, `oap60_omega/directed`, `oap61`
  (bounded ω-complete ⇒ `OUSArchimedean`), `wright_normComplete`
  (⇒ `OUSNormComplete`), the relative-supremum toolkit `IsLUBIn`, `symIcc`,
  `affIso`, `exists_isLUB_of_symIcc`.
* Gudder–Pulmannová: instance `gpOrderUnitSpace` on `GP.Vec E` (unit
  `GP.gunit`), `gmap_le_gmap_iff`, `gmap_perp_iff`, `gpEquiv`, `oap62`,
  `gp_omegaComplete`, `gp_directedComplete`, `gp_archimedean`, `gp_sup`,
  and `vecLattice` (an `abbrev`, so the lattice's `≤` is definitionally the
  given order — needed for Yosida's `[Lattice V] [OrderUnitSpace V]`).
* Representations: `IsUnitRep u e` (order iso of `M` onto `[0,u]`
  preserving `⊥`, `⋁`, `1`, scalars), `IsUnitRep.comp`, `.toHom`,
  `.toHom_isIso`, `.mul_apply` (the transported product is pointwise);
  topology: `RelSup`, `isOpen_closure_of_relSup`,
  `basicallyDisconnected_of_relSup`, `extremallyDisconnected_of_relSup`.

Hints for `Main.lean` (OAP 68–73) — re-derive routes from the print:

* OAP 68/69 are OAP 54/57 with OAP 66 applied to the convex factor `M₁`;
  compose `EMEmbedding`/`EMIsIso` with `oap66`'s `f` and Basic's
  `prodEffectMonoid`.  OAP 66 needs `OmegaComplete M₁` for the *factor*
  (not only for `M`), and `oap37` for `M₁`.
* OAP 70 (commutativity): `oap7_CX` gives commutativity of
  `[0,1]_{C(X)}`; Boolean algebras are commutative (`oap6_commutative`);
  the print's "join" for `B`'s multiplication is the meet (PLAN flag).
* OAP 71 (no zero divisors ⇒ `{0}`, `{0,1}` or `[0,1]`): the convex case goes
  through `oap66`; a point `X` with two points gives zero divisors via
  Urysohn (`exists_continuous_zero_one_of_isClosed`, already imported here).

Pitfalls met here:

* This Mathlib's `add_le_add_left h c : a + c ≤ b + c` and
  `add_le_add_right h c : c + a ≤ c + b` (swapped from older Mathlib); the
  tree's `ou_add_le_add_right` is unambiguous.
* `IsLUB` takes `[LE α]`: with an explicit instance write
  `@IsLUB _ (@eaPartialOrder _ inst).toLE S s`.
* Structure projections of `EffectMonoidHom` into `Set.Icc (0 : C(X,ℝ)) 1`
  (`f.toFun`) fail to elaborate in a *statement* unless the effect monoid on
  the interval is an instance (hence the local instance above).
