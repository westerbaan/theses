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

* **OAP 22** (`lem:forcing`, first.tex:727, Lemma), proof, first line — typo:
  "Since `a ≤ a'` and `b ≤ b'`" should read "Since `a ≤ b` and `a' ≤ b'`".
  Statement unaffected (`Papers.OAP.oap22_forcing`).

* **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), third clause —
  **false as printed.**  For `S ⊆ [x,1]` the print reads
  "`⋀_{s∈S} s ⊖ x` exists ⟹ `(⋁S) ⊖ x = ⋁_{s∈S} s ⊖ x`"; the premise must be
  `⋁_{s∈S} s ⊖ x` (a supremum).  As printed it fails already for `x = 0`: in
  the Wright triangle `{a₁, a₂}` has infimum `0` but no supremum.  Lean:
  `Papers.OAP.oap24_3_false_as_printed` (refutation), `Papers.OAP.oap24_3`
  (corrected clause).

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

* **OAP 70** (first.tex:2592, Corollary), proof — slip: "The multiplication
  in `B` is given by the join"; the multiplication of a Boolean algebra as an
  effect monoid is the *meet* (Example 6).  The argument only needs it to be
  commutative, so the corollary is unaffected.  Lean: `Papers.OAP.oap70`.

## EJA — *Pure Maps between Euclidean Jordan Algebras* (arXiv:1805.11496, `1805.11496/main.tex`)

### EJA 3 (main.tex:212, Example) — inner product not real for `F = ℍ` (2026-09-26)

The print puts `⟨A, B⟩ := tr(AB)` on `M_n(F)^sa` for `F ∈ {ℝ, ℂ, ℍ}`.  For
`F = ℍ` this is not real-valued: in `M₂(ℍ)^sa` take `A` with off-diagonal
entries `i, −i` and `B` with `j, −j`; then `tr(AB) = −2k`.  The real part
`Re tr(AB)` is meant (for `ℝ` and `ℂ` the two agree on self-adjoint
matrices).  Lean: `Papers.EJA.hermMat_inner` (inner product `re tr (AB)`),
`Papers.EJA.matrix_examples`; refutation `Papers.EJA.example3_trace_not_real`.

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

### EJA 27 (`theor:polardecomp`, main.tex:647, Theorem) — gap in the proof (2026-09-26)

The last step claims that `ΦΦ*` being a projection with `(ΦΦ*)(1) = ⌈Q_q p⌉`
"is sufficient to conclude that `ΦΦ* = Q_{⌈Q_q p⌉}`".  That inference is not
valid in general: in `M₂(ℝ)^sa` the trace-orthogonal projection onto `ℝ·1`,
`x ↦ ½ tr(x)·1`, is a positive projection fixing `1` but is not `Q_1 = id`.
Repair (statement unaffected): by the fundamental formula
`ΦΦ* = Q_q Q_p Q_{c²} Q_p Q_q = Q_{Φ(1)}` (`c = (Q_p q²)^{-1/2}`); `ΦΦ*` is
idempotent because `Φ*Φ = Q_e` and `Φ Q_e = Φ`, so `Q_{Φ(1)²} = Q_{Φ(1)}`,
whence `Φ(1)` is an idempotent, and `⌈Φ(1)⌉ = ⌈Q_q p⌉` by comparing zero
patterns.  Lean: `Papers.EJA.polardecomp`.

### EJA 34 (`super-duper-theorem`, main.tex:775, Theorem) — hidden hypothesis

Def 32 calls `g` ⋄-positive when `g = f ∘ f` for some ⋄-self-adjoint `f`,
without asking `f` to be pure; the proofs of 34 and 39 use that `f` is pure
(to decompose it as filter ∘ corner).  With that hypothesis both hold (39's
printed proof also needs the repair of EJA 38 above).  Lean:
`Papers.EJA.super_duper_theorem`, `Papers.EJA.eja39` (root assumed pure).
**Statements true as printed** (2026-09-26): a ⋄-self-adjoint `f` with `f ∘ f`
pure is itself pure (the pure square reflects order and is injective on
`E₁(⌈f(1)⌉)`, so `f` is there a positive bijection with positive inverse; finite
dimension replaces the tree's B15 Schur/Gardner step;
`docs/research/eja-b15.md`).  Lean: `Papers.EJA.diaSA_root_isPure`,
`Papers.EJA.eja34'`, `Papers.EJA.eja39'` (root not assumed pure).

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

### EJA 40 (main.tex:916, Theorem) — inherits the gap of EJA 34

The proof gets the `&`-effectus axiom 211II.1 (a *unique* ⋄-positive `asrt_p`
with `asrt_p(1) = p`) from EJA 34.  But 211II.1 quantifies over ⋄-positive maps
in the sense of eff.tex 206II.4 / Def 32, `g = f ∘ f` with `f` ⋄-self-adjoint
and **not** assumed pure, while 34's printed proof covers only pure `f`
(above).  So the uniqueness of `asrt_p`, and with it the theorem, rests on 34
for non-pure roots (the analogue of thesis B's B15 for `vNᵒᵖ`).  The gap is
closed: a ⋄-self-adjoint root of a pure map is itself pure
(`Papers.EJA.diaSA_root_isPure`), so 34 holds as printed (`Papers.EJA.eja34'`)
and the theorem stands.  Everything
else in the proof is correct: existence of `asrt_p = Q_{√p}`, purity of `π∘ξ`
(EJA 31), and the three conditions of 215III (the second is the fundamental
formula).  Lean: `Papers.EJA.eja40` (with the hypothesis
`Papers.EJA.Eja34Literal`, discharged by `eja34'`), `Papers.EJA.eja40_of_pureRoot`.

## REC — *A computer scientist's reconstruction of quantum theory* (arXiv:2109.10707, `2109.10707/short.tex`)

* **REC 7** (`ex:orthomodularlattice`, short.tex:374, Example) — **false as
  printed**, the same slip as OAP 2 (the example is copied from there).  The
  print makes an orthomodular lattice an effect algebra with
  `x ⊥ y ⟺ x ∧ y = 0` and `x ⊻ y = x ∨ y`; in `MO2` both `a ⊻ a^⊥ = 1` and
  `a ⊻ b = 1` with `b ≠ a^⊥`, so orthosupplements are not unique.  Repair:
  `x ⊥ y ⟺ x ≤ y^⊥`; the two agree in a Boolean algebra, the only case used
  later (REC 16).  Lean: `Papers.REC.rec7_as_printed_false` (refutation),
  `Papers.REC.rec7_corrected` (repaired claim, with the order clause).

* **REC 44** (`def:JB-algebra`, short.tex:861, Definition) — the product is only
  required to be a "binary operation"; a JB-algebra (Hanche-Olsen–Størmer 3.1.6,
  which the point cites) is a Jordan *algebra*, so the product must be bilinear.
  Lean: `Papers.REC.JBAlgebra` adds `add_mul`, `smul_mul`.

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

* **REC 89** (short.tex:1516, Proposition), second bullet — **false as
  printed**: separation by states does not pass to `Split(C)`.  If `C` has an
  idempotent scalar `s ∉ {0, 1}`, the object `(I, s)` of `Split(C)` has no states
  (a state `ω` would satisfy `ω = s ∘ ω` and `1 = s ∘ ω`, whence `s = 1`) but two
  distinct endomorphisms `id = s` and `0`.  `Kl(𝒟_M)` on finite sets with
  `M = 𝒫(ℕ)` is separated by states and has such scalars.  The printed "works
  analogously" fails because the analogue of `p ∘ s` is `t ∘ ω`, a substate.
  Nothing later uses this bullet (REC 90 needs no separation).  Lean:
  `Papers.REC.rec89_states_not_preserved`, `Papers.REC.rec89_states_false_as_printed`.

* **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition) — **false as
  printed for separation by predicates**; true for separation by states.  The
  proof takes `asrt_{s∘1}`, which needs `s ∘ 1` sharp, without saying why.  Under
  state separation it is: `⌊s∘1⌋` agrees with `s ∘ 1` on every state, because
  `ω ∘ s` factors through the comprehension of `s ∘ 1`.  Under predicate
  separation it need not be.  Counterexample ("linked points", review
  2026-09-26, second review CONFIRMED): the subcategory of `Pfn × Pfn` on triples
  `(a, l, r)` of finite sets, `X₁ = a ⊔ l`, `X₂ = a ⊔ r`, with maps the pairs of
  partial functions satisfying `f₁⁻¹(y) = f₂⁻¹(y) ⊆ a` for linked `y`.  It is
  an effectus separated by predicates (`Pred(X) = 2^{X₁} × 2^{X₂}`), with images
  and compatible filters and comprehensions, and scalars `{0,1}²`.  For
  `s = (1,0)` and the object `A` with one linked point, `s·id_A = (id, 0)` is not
  a map and `s ∘ 1_A` is not sharp.  The effectus is not equivalent, even as a
  bare category, to a product of two non-trivial effectuses (`End(A) = {0, id}`
  puts `A` in one factor, and `A` maps non-trivially to every non-zero object).
  The correct statement assumes that `s ∘ 1_A` and `s^⊥ ∘ 1_A` are sharp for all
  `A`; state separation or a monoidal structure (REC 91) implies this.  Lean:
  `Papers.REC.rec92_false_as_printed`, `Papers.REC.rec92_counterexample`
  (refutation), `Papers.REC.rec92_states` (as printed), `Papers.REC.rec92_predicates`
  (with the sharpness hypothesis), `Papers.REC.isSharp_of_states`.

* **REC 99** (short.tex:1816, Proposition) — **false as printed** (independent
  review 2026-09-26; refuted in Lean).  `Kl(𝒟_M)` on finite sets with
  `M = 𝒫(ℕ)` is directed complete (`Pred(Y) = M^Y`) and has finite tomography
  (the point predicates `δ_y`: `(δ_y ∘ f)(x) = f(x)(y)`), but
  `Pred(I) = 𝒫(ℕ) ≇ 𝒫(A) ⊕ [0,1]^n` for finite `A` — not even as ordered sets.
  The proof's error: at the object `I` finite tomography is witnessed by
  `p = id_I` alone, so "the `p_i` separate `Pred(I)`" constrains nothing; in
  fact every complete Boolean algebra occurs as the scalars of a
  directed-complete effectus with finite tomography.  What the proof aims at
  holds exactly when `Pred(I)` has finitely many idempotents: then
  `Pred(I) ≅ 𝒫(A) ⊕ [0,1]^n` (from REC 34), and conversely.  Lean:
  `Papers.REC.rec99_false_as_printed`, `Papers.REC.rec99_any_boolean_scalars`,
  `Papers.REC.rec99_corrected`, `Papers.REC.rec99_corrected_converse`.

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

### REC 104 — false as printed; sequential effectuses have irreducible scalars (2026-09-26, refuted in Lean)

* **REC 104** (short.tex:1877, Remark) — **false as printed**.  The remark says
  that in Theorem 102 the scalars of a sequential effectus "can satisfy
  `Pred(I) ≅ [0,1]_{C(X)}` where `X` is an arbitrary Stonean space".  They cannot
  unless `X` has at most one point.  In any effectus with filters and
  comprehensions that is separated by states, the only idempotent scalars are `0`
  and `1`.  For an idempotent `s ≠ 1`, a state `σ` of the comprehension `{I|s}`
  would give `π_s ∘ σ = 1` and hence `s = 1`.  So `{I|s}` has no states, and
  separation makes `id_{I|s} = 0`, whence `π_s = 0` and `s = 0`.  A
  non-trivial clopen of `X` gives a non-trivial idempotent of `[0,1]_{C(X)}`.
  Hence every sequential effectus has irreducible scalars (`{0}`, `{0,1}` or
  `[0,1]`, REC 36).  Consequences:
  - the product in Theorem 102 always has a trivial factor, so 102 is the case of
    Theorem 103 (whose irreducibility hypothesis is automatic);
  - the JB-vs-JBW distinction the remark motivates does not come from the
    scalars;
  - REC 92's state-separated case has no instances: its hypotheses leave no
    non-trivial idempotent scalar;
  - the `C(X)`-valued concerns in the REC 120 entry above do not arise.

  Theorems 102 and 103 remain true.  Lean:
  `Papers.REC.rec104_false`, `Papers.REC.idem_scalar_trivial`,
  `Papers.REC.scal_irreducible_of_states`, `Papers.REC.rec102_trivial_factor`.

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

### SEA 71 (`lem:multfloor`, second.tex:2095, Lemma), proof — two slips (2026-09-26)

After `a ∘ b² = a` the print writes "`a ∘ b⁴ = 0`", "`a ∘ b^{2ⁿ} = 0`" and
"`a ∘ bⁿ = 0`" where it means `= a` throughout, and "since `bⁿ ≤ b^{2ⁿ}`" is
reversed (powers decrease: `b^{2ⁿ} ≤ bⁿ`, whence `a = a ∘ b^{2ⁿ} ≤ a ∘ bⁿ ≤ a`).
The statement is unaffected; induction on `n` (`a ∘ bⁿ⁺¹ = (a ∘ b) ∘ bⁿ`, as
`a | b`) avoids the powers of 2.  Lean: `Papers.SEA.sea71_floor`.

### SEA 73 (`prop:assoc-a-convex`, second.tex:2129, Proposition) — needs `E ≠ {0}`; one step of the proof (2026-09-26)

False as printed for the one-element SEA `{0 = 1}`: it is a normal
associative a-convex factor (`Z(E) = {0} = {0,1}`), but a horizontal sum of
copies of `[0,1]` always has `0 ≠ 1`.  Repair: assume `0 ≠ 1`.  In the proof,
for `S ⊆ {0,1}` one has `S'' = Z(E) = {0,1}`, not "`{0,1} = S'' = E`", so the
claim `S'' ≅ [0,1]` holds only for `S ⊄ {0,1}` (which is all that is used).
Lean: `Papers.SEA.sea73_false_as_printed` (refutation),
`Papers.SEA.sea73_assoc_factor` (with `(1 : E) ≠ 0`).

## FDS — *The universal property of infinite direct sums in C\*- and W\*-categories* (arXiv:1907.04714, `1907.04714/direct_sums.tex`)

* **FDS 4.5** (direct_sums.tex:504, Remark) — **ill-typed / false as
  printed.**  For a family `(Aᵢ)ᵢ` the terms `fᵢ fⱼ*` of `∑ᵢⱼ Kᵢⱼ fᵢ fⱼ*`
  (`fⱼ* : B → Aⱼ`, `fᵢ : Aᵢ → B`) compose only when `Aᵢ = Aⱼ`; and for a
  positive semidefinite `K` with some `Kⱼⱼ = 0` (e.g. `K = 0`) the "norm"
  `‖∑ᵢⱼ Kᵢⱼ fᵢfⱼ*‖^½` is only a seminorm, so the space is not a Banach space.
  Repair: a constant family `Aᵢ = A` (as in the remark's own example
  `Aᵢ = ℂ`) and `Kⱼⱼ ≠ 0` for all `j`; then completeness does go "the same way
  as Lemma 4.1".  Lean: `Papers.FDS.KSum.kernel_complete`.

*Update 2026-09-26:* the gap is closed. `Papers.EJA.diaSA_root_isPure` (`PureRoot.lean`) proves that a ⋄-self-adjoint root of a pure map is pure, so EJA 34 holds as printed and EJA 40 follows without extra hypotheses; only the printed proofs of 34 and 39 are incomplete.

## SIG — *Dichotomy between deterministic and probabilistic models in countably additive effectus theory* (arXiv:2003.10245, `2003.10245/main.tex`)

* **SIG 33** (`prop:wmod-effectus`, main.tex:964, Proposition) — imprecise
  ("with scalars `M`").  A scalar of `WMod[M]` is an action-preserving map
  `M → M`, i.e. a right multiplication `t ↦ t·r` (`r = p(1)`), and the
  composite `s ∘ r` is `t ↦ t·r·s`; so `p ↦ p(1)` is an isomorphism of effect
  monoids onto the *opposite* monoid `Mᵒᵖ`, not onto `M`.  The printed claim
  holds only when `M ≅ Mᵒᵖ` (e.g. `M` commutative, which by SIG 42 covers every
  σ-effect monoid, so the σ-half is unaffected in substance).  The `Mᵒᵖ`
  reading is the one Proposition 34 needs: `sSt : C → WMod[Mᵒᵖ]` preserves
  scalars, and `(Mᵒᵖ)ᵒᵖ = M`.  Repair: "with scalars `Mᵒᵖ`" (equivalently,
  `WMod[Mᵒᵖ]` has scalars `M`).  Lean: `Papers.SIG.WMod.effectus_scalars :
  EMIso (Scal (WMod M)) (MOp M)`; for `EMod[M]ᵒᵖ` the scalars are `M` as
  printed (`Papers.SIG.EMod.effectus_scalars`).
