# EJA — plan (phase 1, 2026-09-26)

Paper: A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between
Euclidean Jordan Algebras*, QPL 2018 (EPTCS 287), arXiv:1805.11496.
Source `../papers/1805.11496/main.tex`; index `../papers/EJA-points.csv`
(54 points, one global counter).  Tree: `Theses/B/Eff/JordanAlgebras.lean`
(cited below as **T**) and `docs/research/eja-dagger.md` (cited as **R**).

## 0. The one definitional decision: which EJAs

The paper's EJA (Def 1) is a **possibly infinite-dimensional** real Hilbert
space with a unital commutative Jordan product and `⟨a*b,c⟩ = ⟨b,a*c⟩`
("JH-algebra with unit"); the appendix proves each such `E` is
`E_fin ⊕ ⨁ (infinite-dimensional spin factors)` (Cor 54).  The tree's
`EuclideanJordanAlgebra` (**T** 189aIII) is the classical **finite-dimensional
formally real** one, with order = cone of sums of squares, and carries only
the trace form `ejaB`, not a given inner product.

Decision:
* `Prelim.lean` defines the paper's notion as a Prop-mixin `PaperEJA` over
  Mathlib's `InnerProductSpace ℝ E` + `CompleteSpace E` (Def 1 verbatim), and
  proves the bridge: a finite-dimensional `PaperEJA` is a tree
  `EuclideanJordanAlgebra` (via **T** `ofForm`), with the given inner product
  as an associative form.  The appendix (41–54) is about `PaperEJA` itself.
* §2–§4 (points 5–40) are formalised over the tree class, i.e. **in finite
  dimension**.  Where a statement mentions the inner product it is stated for
  an **arbitrary** associative positive-definite symmetric form `β`
  (`EJAForm V`: exactly what a finite-dimensional `PaperEJA`'s inner product
  is), not only the trace form; so nothing depends on the choice.  The
  finite-dimensionality is recorded in every audit row as the deviation
  `fin-dim`.  Lifting §2–§4 to infinite-dimensional `PaperEJA` needs the
  appendix's spectral theorem (Cor 46) for `PaperEJA` and then every tree
  lemma re-proved without `FiniteDimensional` (the tree uses it for the
  minimal polynomial, `LinearMap.trace` and Riesz); that is a separate,
  expensive job (est. 4–6k lines) and is **not** planned.
* Maps: `EJAPSUMap` of **T** (positive subunital linear maps, algebra
  direction), category `EJAPsu`.

## 1. Point table

Kind abbreviations: D definition, N note, E example, T theorem, P proposition,
L lemma, C corollary, No notation.  "tree" = already in **T**, needs a thin
restatement.  Cost = new Lean lines, rough.

| # | kind | content | target | deps (points / tree) | status / missing | cost |
|---|---|---|---|---|---|---|
| 1 | D | Jordan algebra; EJA = Hilbert space + `⟨ab,c⟩=⟨b,ac⟩` | Prelim | **T** `ofForm`, `formallyReal_of_form` | `PaperEJA` + fin-dim bridge | 150 |
| 2 | N | classically finite-dimensional; = unital JH-algebra | Prelim | 1 | doc only (bridge is the content) | 0 |
| 3 | E | `M_n(F)^sa`, `F ∈ {ℝ,ℂ,ℍ}`; `M_3(𝕆)^sa` | Examples.lean (later) | 1 | ℝ,ℂ via `RCLike` + `ofForm` ~400; ℍ needs a star-ring version ~250 more; **𝕆 not in Mathlib** (octonions + Jordan identity for `M_3(𝕆)`: ~1.5k, defer) | 400–2k |
| 4 | E | spin factor `H ⊕ ℝ` | Prelim | 1 | new; also gives the counterexample to 9.4 | 250 |
| 5 | D | positive = square; positive/unital/subunital map; `EJA_psu` | Prelim | **T** `eja_nonneg_iff_exists_sq`, `EJAPSUMap`, `EJAPsu` | tree, thin | 40 |
| 6 | D | state; effect ↔ `0≤a≤1` | Prelim | **T** `ejapsu_pred_val`, `eja_stat_state` | tree, thin | 30 |
| 7 | T | cone; strong Archimedean unit; OUS; norm equiv.; self-dual; JBW | Prelim (items 0,1,2,4); Appendix (3,5) | **T** `eja_isSumSq_iff_exists_sq`, `eja_exists_isSumSq_nsmul_one_sub`, `toOrderUnitSpace`, `eja_nonneg_of_forall_idem` | self-duality new for general `β`; Archimedean `a ≤ 1/n ⇒ a ≤ 0` new (spectral); item 3 needs an order-unit norm (none in **T**); item 5 = 51 | 250 |
| 8 | D | `L_a`, `Q_a = 2L_a² − L_{a²}` | Prelim | **T** `ejaLm`, `ejaU` | tree, thin | 10 |
| 9 | P | `Q_1=id`; `Q_a1=a²`; `Q_a` β-self-adjoint; `Q_ab=0⇔Q_ba=0⇔a*b=0`; FF `Q_{Q_ab}=Q_aQ_bQ_a`; `Q_a` invertible ⇔ `a` invertible; `Q_a` positive | Prelim (1,2,3,4,7); FF.lean (5); Prelim or later (6) | **T** `ejaU_one`, `ejaU_apply_one`, `eja_U_nonneg'` | **9.4 FALSE as printed** for arbitrary `a,b` (see §2); true for `a,b ≥ 0`.  **9.5 = FF not in T** (R §5 item 11: 1.5–2.5k, high risk).  9.6 needs Jordan inverses (~300, via one-family law **T** `eja_U_family_comp'`) | 9.4: 250; 9.5: 2k; 9.6: 300 |
| 10 | D | idempotent (positive, ≤1); atomic; orthogonal ⇔ `⟨p,q⟩=0` | Prelim | **T** `eja_idem_nonneg`, `eja_idem_le_one`, `EJAPrimitive`, `eja_idem_split` | atomic ⇔ **T** primitive: new; orthogonality for general β: new | 150 |
| 11 | P | `Q_p` idempotent; for effects `Q_pa=0⇔⟨a,p⟩=0`, `Q_pa=a⇔a≤p⇔p*a=a` | Prelim | 9, 10; **T** `ejaPone_idem`, `ejaU_idem`, `eja_pone_eq_self_iff` | proof avoids FF (tree has `Q_p²=Q_p` directly) | 150 |
| 12 | P | spectral theorem with *atomic* idempotents | Prelim | **T** `eja_spectral`, `eja_idem_split`, `eja_V1_lt` | refinement to atomic: new (induction on `finrank V₁(p)`) | 150 |
| 13 | P | `⌈a⌉` least idempotent above an effect; `⌊a⌋` greatest below | Prelim | 11, 12; **T** `eja_exists_supp`, `eja_exists_floor` | define `ejaCeil` for all `a` (least idempotent `p` with `p*a=a`), `ejaFloor` | 200 |
| 14 | D | corner for an effect `q` (initial) | FilterCorner | 5 | forward reference: codomain `{E|q}` is only defined in Def 20; formalise with arbitrary codomain (as the following text uses it) | 30 |
| 15 | N | name "corner" | — | — | doc only | 0 |
| 16 | D | filter for `q` (final) | FilterCorner | 5 | same remark as 14 | 30 |
| 17 | N | name "filter" | — | — | doc only | 0 |
| 18 | D | pure = filter ∘ corner | FilterCorner | 14, 16 | | 10 |
| 19 | P | Peirce: `E_1(p) = Q_p(E)` sub-EJA = fixed points | FilterCorner | **T** `EJACorner`, `eja_pone_eq_self_iff`, `eja_mul_pone` | tree, thin (+ range = fixed set) | 40 |
| 20 | D | `{E|q} := E_1(⌊q⌋)`, `E_q := E_1(⌈q⌉)` | FilterCorner | 13, 19 | | 20 |
| 21 | L | `ω(p)=ω(1) ⇒ ω(Q_pa)=ω(a)` (Cauchy–Schwarz) | FilterCorner | 10 | new, paper's argument | 60 |
| 22 | C | same for positive `g : E → W` | FilterCorner | 21; **T** `eja_exists_state_ne_zero` | new | 30 |
| 23 | L | `g(q)=g(1) ⇒ g(⌊q⌋)=g(1)` | FilterCorner | 13 | new | 60 |
| 24 | P | standard corner `π_q = r∘Q_{⌊q⌋}` is a corner | FilterCorner | 22, 23; **T** `ejaPoneCorner`, `eja_pone_nonneg` | **T** proves the effectus form inside `ejapsuHasComprehension` by a different (Peirce) argument; re-prove by the paper's | 120 |
| 25 | P | standard filter `ξ_q = Q_{√q}∘ι` is a filter | FilterCorner | 11, 13; **T** `eja_exists_filter`, `eja_U_nonneg'`, `eja_corner_of_le_smul` | needs `√q` as a *function* + uniqueness of the positive square root (not in **T**; R §2 item 12) | 250 |
| (text) | — | `ξ_q∘π_{⌈q⌉} = Q_{√q}`; isos are pure | FilterCorner | 24, 25 | R §5 item 2 | 120 |
| 26 | D | adjoint `Φ*`; partial isometry | Polar | β | | 30 |
| 27 | T | polar decomposition | Polar | 9.5 (FF), 13, 29, 9.6-style pseudo-inverses | **needs FF (general)**; also cites Kadison–Ringrose 6.1.1 (`Φ*Φ` proj ⇒ `ΦΦ*` proj) | 900 |
| 28 | D | image of a positive map | Polar | 13 | | 10 |
| 29 | P | every positive map has an image, an idempotent | Polar | 23; **T** `ejapsu_exists_image` | tree (effectus form), thin restatement + minimality over *effects* | 80 |
| 30 | P | `π_p∘ξ_q = ξ_a∘Φ∘π_b` | Polar | 27 | FF | 400 |
| 31 | C | pure maps compose | Polar | 30; filters compose (thesis B 197IX), corners compose | FF | 250 |
| 32 | D | `f^⋄`, `f_⋄`, ⋄-adjoint, ⋄-s.a., ⋄-positive | Diamond | 13, 28 | direction clash: `f^⋄(p)=⌈p∘f⌉` reads `f` in the effectus (opposite) direction, the rest of the paper in the algebra direction | 60 |
| 33 | P | self-adjoint ⇒ ⋄-s.a.; `Q_a` ⋄-s.a.; `Q_a` ⋄-positive for `a ≥ 0` | Diamond | 32, 9.3; one-family law (**T**) instead of FF for `Q_a = Q_{√a}²` | "self-adjoint operator" must be *positive* (subunital) for ⋄ to be defined — implicit | 250 |
| 34 | T | pure ⋄-positive `g` ⇒ `g = Q_{√g(1)}` | Diamond | 39, 31 | proof through 38 (see §2); B15-style hidden hypothesis: the ⋄-s.a. root `f` is used as *pure* | 300 |
| 35 | L | order-sharp ⇔ idempotent | Diamond | 12, 11; **T** `ejapsu_isSharp_iff` | new (direct, paper's proof) | 80 |
| 36 | P | unital order iso ⇒ Jordan iso | Diamond | 35, 12 | new | 250 |
| 37 | C | `Θ∘Q_a = Q_{Θa}∘Θ` | Diamond | 36 | new | 60 |
| 38 | L | faithful pure ⋄-s.a. `f` ⇒ `f = Q_{√f(1)}∘Θ`, `Θ(√f(1)) = √f(1)`, `Θ=Θ⁻¹` | Diamond | 36, 37, 24, 25 | **FALSE as printed** (see §2) | — |
| 39 | P | faithful pure ⋄-positive `g` ⇒ `g = Q_{√g(1)}` | Diamond | 38 | printed proof goes through the false 38; statement survives the counterexample; needs a new proof | 500? |
| 40 | T | `EJA_psu^op` is a †-effectus | Diamond / Dagger.lean | 24, 25, 29, 31, 34, FF, √-uniqueness; **T** `diamond_effectus_eja` | needs FF (R §2: axiom (2) *is* FF) and everything above | 800 |
| 41 | P | `‖a*b‖ ≤ r‖a‖‖b‖` (uniform boundedness) | Appendix | 1; Mathlib `banach_steinhaus` | new, for `PaperEJA` | 120 |
| 42 | No | powers, `L_a`, commutator | Appendix | — | | 10 |
| 43 | P | `[L_a,L_{a²}]=0` etc.; `L_{a(bc)}` formula; power-associativity | Appendix | Mathlib `Algebra/Jordan/Basic`; **T** `eja_lin`, `eja_pow_mul_pow` (tree class only) | restate for any commutative Jordan algebra over ℝ | 200 |
| 44 | C | closure of the algebra generated by `a` is associative | Appendix | 41, 43 | new | 150 |
| 45 | P | associative EJA ≅ `ℝⁿ` | Appendix | Kadison representation theorem | **Kadison's theorem not in Mathlib**; direct Hilbert-space proof needs spectral theory of self-adjoint operators on a *real* Hilbert space (not in Mathlib) | 1.5–3k |
| 46 | C | spectral theorem (for `PaperEJA`) | Appendix | 44, 45 | fin-dim: **T** `eja_spectral` | 50 |
| 47 | P | self-duality | Appendix | 46; cites Chu p.107 | fin-dim: as 7.4 | 80 |
| 48 | C | positive cone additive; Archimedean OUS | Appendix | 47, 45 | fin-dim: **T** | 60 |
| 49 | P | Hilbert and order-unit norms equivalent | Appendix | 46, 47 | new (needs an order-unit norm) | 250 |
| 50 | P | EJA is a JB-algebra | Appendix | 49; Alfsen–Shultz 1.11 | JB-algebras not in Mathlib; state the defining inequalities only | 200 |
| 51 | P | bounded directed complete; states normal | Appendix | 47; Riesz | new | 250 |
| 52 | P | idempotent = finite sum of atomic idempotents | Appendix | 45, 46 | fin-dim: as 12 | 100 |
| 53 | P | type I JBW of finite rank | Appendix | 50–52 | JBW-algebras not in Mathlib | 150 (defs) |
| 54 | C | `E ≅ E_fin ⊕ ⨁ spin factors` | Appendix | 53; Hanche-Olsen–Størmer classification of JBW factors | classification not formalisable at reasonable cost; **out of reach** | — |

## 2. False or under-specified as printed

* **EJA 9.4 is false as printed.**  "For any EJA `E` and `a,b,c ∈ E`:
  `Q_ab = 0 ⇔ Q_ba = 0 ⇔ a*b = 0`."  In the spin factor `ℝ² ⊕ ℝ`
  (`≅ M₂(ℝ)^sa`) take the idempotent `a = (e₁/2, 1/2)` and `b = (e₂, 0)`:
  `Q_a b = 0` but `a*b = (e₂/2, 0) ≠ 0` (and `Q_b a = (−e₁/2, 1/2) ≠ 0`).
  In `M₂(ℝ)^sa`: `a = diag(1,0)`, `b` = the flip.  The cited Alfsen–Shultz
  Lemma 1.26 is for **positive** `a, b`; the paper only ever uses 9.4 for
  positive elements (Prop 11's proof), so the fix is "for positive `a,b`".
  Formalised both ways in `Prelim.lean` (`spin_Q_ne_mul_counterexample`,
  `eja_Q_eq_zero_iff_mul_eq_zero`).
* **EJA 38 is false as printed** (not yet in Lean; needs a break-it review
  before it is filed).  `E = ℝ ⊕ ℝ`, `q = (a,b)` with `0 < a ≠ b ≤ 1`,
  `Θ` = the swap, `f = Q_q ∘ Θ`, `f(x,y) = (a²y, b²x)`.  `f` is pure
  (`Θ` is a corner for `1`, `Q_q` the standard filter of `q²`, `⌈q²⌉ = 1`),
  faithful, and ⋄-self-adjoint: `f^⋄ = f_⋄ = swap` on `Idem(ℝ²) = {0,1}²`
  (equivalently, the paper's own criterion `⟨f s,t⟩ = 0 ⇔ ⟨s,f t⟩ = 0`
  holds since `f`'s zero pattern is symmetric).  `√f(1) = q` is invertible,
  so the `Θ` of the conclusion is forced to be the swap, and
  `Θ(√f(1)) = (b,a) ≠ q`.  The broken step is "by uniqueness of such
  decompositions … the `p_j` and `r_j` agree" (main.tex ~line 865): equal
  *sets* of eigenvalues do not give `μ_i = λ_i²` index-wise.  Prop 39 is not
  refuted by this example (`g = f∘f = a²b²·id = Q_{√g(1)}`), and it holds in
  `M_n(ℂ)^sa` by a direct argument (a ⋄-s.a. `f = Q_q∘Ad_u` forces
  `(qu)* = λ qu`), but its printed proof goes through Lemma 38's false
  conclusions `Θ(q) = q` and (via `Θ Q_q = Q_q Θ`) `Θ = Θ⁻¹`.  So 39, 34 and
  40 are **unproven as printed**, not known false.  **R §1 repeats the
  broken step** ("`Θ(q) = q` (an eigen-decomposition matching argument)").
* **B15 recurs** (R §1): Def 32 does not require the ⋄-self-adjoint root of a
  ⋄-positive map to be pure; Prop 39's proof assumes it.
* Def 14/16 name the codomain `{E|q}` / domain `E_q` before Def 20 defines
  them; the text after them uses arbitrary (co)domains.  Formalised with
  arbitrary objects.
* Def 32 reads `f` in the effectus direction (`p∘f`), the rest of the paper in
  the algebra direction.
* Prop 33 "any self-adjoint operator" must mean a positive (subunital) one.
* Prop 13 defines `⌈a⌉` for effects only, Thm 27 applies it to positive
  elements (harmless: scale).
* Prop 41's proof: `(‖a*b‖₂)² ≤ r_b ‖a*b‖₂` should read `r_a`.
* Prop 30's proof: "`Θ∘π_{⌈q&p⌉} = f̄`" names the iso `Θ`, the statement `Φ`;
  `r_j = Σ_{μ_i=μ_j} q_j` in Lemma 38 should be `q_i`.
* Prop 52's proof applies Prop 45 to the (non-closed, non-unital) span of the
  `q_i`; it needs the closed unital subalgebra they generate.

## 3. Missing infrastructure, in order of need

1. `ejaSqrt` + uniqueness of positive square roots (for 25, 33, 40): ~200.
2. `ejaCeil`/`ejaFloor` as functions (13): ~200.
3. **Fundamental formula** (9.5; needed by 27, 30, 31, 40): the tree
   deliberately avoids it; R §1 sketches a Macdonald-free route
   (two-valued reduction), 1.5–2.5k lines, high risk.  FF *at an idempotent*
   is cheap (~400, R §5 item 9) and may suffice for 30 if the rank argument of
   R §1 works.
4. Jordan isomorphisms, unital order isos (36, 37): ~300.
5. For the appendix: a real-Hilbert-space spectral argument or Kadison
   representation (45) — the blocker for everything infinite-dimensional.

## 4. Files and order

1. `Papers/EJA/Prelim.lean` — §2, points 1, 2, 4–13 (+ spin factors,
   9.4 counterexample).  No new infrastructure beyond **T**.
2. `Papers/EJA/FilterCorner.lean` — §3, 14–25 + the text after 25
   (needs 1 above; imports `Prelim`).
3. `Papers/EJA/Appendix.lean` — 41–44 (algebraic/analytic parts that need
   only `PaperEJA`); 45–54 only after a decision on Kadison.
4. `Papers/EJA/FF.lean` — the fundamental formula (9.5).
5. `Papers/EJA/Polar.lean` — 26–31.
6. `Papers/EJA/Diamond.lean` — 32–40, after a break-it review of §2's
   Lemma 38 counterexample and a decision on how to prove 39.
7. `Papers/EJA/Examples.lean` — Example 3 (ℝ, ℂ, ℍ; 𝕆 deferred).

## 5. Status at the end of phase 1 (2026-09-26)

Formalised, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only:

* `Prelim.lean` (1,054 lines; `scripts/lean1.sh` exit 0): EJA 1, 2, 4, 5, 6,
  7 (items 0, 1, 2, 4), 8, 9 (items 1, 2, 3, 4 refuted + corrected, 7 first
  half), 10, 11, 12, 13.
* `FilterCorner.lean` (581 lines): EJA 14, 16, 18, 19, 20, 21, 22, 23, 24,
  25, plus uniqueness of positive square roots and the filter data at `⌈q⌉`.
* `Appendix.lean` (112 lines): EJA 41.

`FilterCorner.lean` and `Appendix.lean` import `Papers.EJA.Prelim`, which has
no olean this session (`lean1.sh` writes none); each was compiled as the
concatenation `Prelim.lean ++ File.lean` (import line stripped), exit 0.  A
proper compile of each needs `Prelim`'s olean first.

Open from §1: 3 (examples), 7.3/7.5, 9.5 (FF), 9.6, 9.7b, the text after 25
(`ξ_q ∘ π_{⌈q⌉} = Q_{√q}`, needs `U_b V ⊆ V₁(⌈b⌉)`), 26–40, 42–54.
Notes 15, 17 carry no formal content.
