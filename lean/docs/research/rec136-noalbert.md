# REC 136 without the Albert map: what the tensor can and cannot replace

Research note, 2026-09-26. All results **claimed** (no Lean, nothing compiled, not reviewed).
Numerics: scratch `r136na-descent.py` (reuses the 27-dim Albert model `r136n-alb.py`).

## 0. Answer in one paragraph

(a) No: REC 136 from `JBWExceptionalSummand` alone is out of reach of the proved
infrastructure, and the tensor data do not close the gap (§4). (b) Yes, twice: the Albert
target can be replaced by (b1) `ExceptionalFiniteQuotient'` — a unital-nonvanishing Jordan hom
into *some* JBW-algebra of dimension `≤ D`, `D` uniform, no Albert structure, no cubic, no
exchangeable families — via a dimension-descent lemma (§2) with `D` tensor factors; or by
(b2) the JBW-intrinsic `ExceptionalNoFourExch` — no four pairwise-exchangeable non-zero
orthogonal idempotents in a purely exceptional JBW-algebra — via the proved exchangeable pair
(`pe_exists_exch_pair`), REC 134 and a central-cover dichotomy (§3), two factors only.
Neither is provable from the infrastructure; (b2) is the exact obstruction (c): every
intrinsic route needs a **rank bound** for purely exceptional JBW-algebras, i.e. the
"purely exceptional ⟹ type I₃" content of H-O–S 7.2.7 (type decomposition + A–S 4.4), which the
tensor cannot supply because everything the infrastructure produces lives, in the would-be
model `C(Y, M₃(𝕆)_sa)`, inside *special* (rank ≤ 2) corners.

## 1. The reusable core: an abelian idempotent in the op-commutant kills everything

**Lemma A (claimed).** `V'` JBW, `S ⊆ V'` the image of a unital Jordan hom `φ : V_W → V'`
with `V_W` purely exceptional and `φ 1 ≠ 0`. If some idempotent `p ≠ 0` op-commutes with `S`
(`T_p T_y = T_y T_p` on `V'`, `y ∈ S`) and the corner `pV'p` is associative, contradiction.
Proof: `Ph p y = 0` for `y ∈ S` (`p(py) = y(pp)`), so `y ↦ U_p y = P₁(p) y` is multiplicative
on `S` (`mul_hom_of_Ph`) and unital onto `p`; `pV'p` is a JBW-algebra (`ECorner`), associative,
so Gelfand (`gelfandL`, `charSet`, as in `centralIdem_not_assoc`) gives a non-zero Jordan hom
`V_W → C(X, ℂ)`. Nothing about `V'` being purely exceptional is used.
Useful converse (claimed): `pV'p` is associative ⟺ no non-zero exchangeable pair below `p`
(`exists_exch_pair` on the corner; conversely central exchangeable `p' ⊥ q'` forces `p' = q' = 0`).
So REC 136 needs only: **some non-zero abelian idempotent op-commuting with one copy of `V_W`.**
The Albert map supplied it through rank (trace-1 idempotents of `S₁`); §2–3 are the two ways
to get it, or a contradiction, without `M₃(𝕆)`.

## 2. (b1) Dimension descent: any uniformly finite-dimensional target suffices

**Prop `ExceptionalFiniteQuotient'`**: `∃ D, ∀ V` non-zero purely exceptional JBW,
`∃ Q` JBW-algebra, `finrank ℝ Q ≤ D`, `χ : V → Q` multiplicative linear, `χ 1 ≠ 0`.
Implied by `ExceptionalAlbertMap` (`Q = Alb`, `D = 27`; needs a `JBWAlgebra Alb` instance —
not in the tree, finite-dimensional EJA ⟹ JBW, est. 200 lines) and by A–S–S Gelfand–Naimark.
It differs from `ExceptionalFiniteQuotient` (Rec136Hyps2) only in asking a JBW target
instead of "kernel is an ideal"; and it drops part (i) entirely.

**Lemma B (descent, claimed).** `Q` JBW, `finrank Q ≤ D`, `S₁, …, S_k ⊆ Q` unital images of
`V_W` (purely exceptional), pairwise op-commuting on `Q`. Then `k ≤ D − 1`.
Step `j`: `S_j ≠ ℝ·unit` (else a character of `V_W`, a Jordan hom into `ℂ`); pick `a ∈ S_j`
not scalar; `exists_nontrivial_idem` gives `p_j ∉ {0, unit}` with `Ph p_j a = 0`, and `p_j`
lies in the norm closure of polynomials in `a` (spectral projections `sproj`; finite dimension
makes sups norm limits), hence op-commutes with `S_i`, `i > j`. Pass to `Q_j := p_j Q_{j−1} p_j`
(`ECorner`, JBW), `S_i^{(j)} := U_{p_j} S_i^{(j−1)}` — still unital images of `V_W` (Lemma A's
multiplicativity) — and op-commutation descends: for `y, z ∈ V₁ ⊕ V₀` and `w ∈ V₁(p_j)`,
`y w = y₁ w` (`V₀V₁ = 0`), so `T_{y₁} T_{z₁} = T_y T_z` on `V₁` (checked numerically). The unit
of `Q_{j−1}` is not in `Q_j`, so `finrank` drops by `≥ 1` per step; `Q_k ∋ p_k ≠ 0` gives
`k ≤ D − 1`. Elementary: Peirce rules, `mul_hom_of_Ph`, `exists_nontrivial_idem`, Gelfand.

REC glue: `X_D := (…(W ⊗ W) ⊗ …) ⊗ W` (`D` factors), `ι_i` by iterated `rec127`; with the
associator every pair `ι_i, ι_j` op-commutes on all of `V_{X_D}` (rebracket as
`X_i ⊗ Y`, then `rec126`). Without associators (as in `Rec136Native`) op-commutation of
`ι_i, ι_j` (`i < j`) holds only on the image `A_j` of `V_{X_j}`; the descent in the order
`1, …, k` still works with nested ambient algebras `U_{p_{j−1}} ⋯ U_{p_1} A_l`, at the cost of
bookkeeping. Then `JBWExceptionalSummand` on `V_{X_D}` as in `tower_absurd`; `χ ∘ π` maps into
`Q`, `k = D` copies contradict Lemma B. Estimate: Lemma B 350–500 lines, glue 200–300; no
Albert cubic, no `ℂ³` coordinates, no `AlbSmallSpan`. Compared with `alb_threeway_nogo`
(three factors, 27-specific), this trades rank counting for `D` factors.

## 3. (b2) The intrinsic Prop: no four exchangeable, via a central-cover dichotomy

**Prop `ExceptionalNoFourExch`**: a purely exceptional JBW-algebra has no four non-zero
pairwise orthogonal idempotents that are pairwise `ExchangeableBySymmetry`.
(Weaker variant `ExceptionalBoundedExch`: `∃ N` uniform, no `N` such idempotents; `⌈log₂ N⌉`
factors.) Implied by Shultz 3.9 (rank ≤ 3 pointwise, all-or-none at points) and by H-O–S
7.2.7's proof (no `I_n`, `n ≥ 4`, `I_∞`, `II`, `III` parts). **Not** implied by
`ExceptionalAlbertMap` or `ExceptionalBoundedRank` (`χ` may kill the family), and not by
A–S 4.4 alone (a special corner with central cover `1` does not make `V` special: rank-2
corners of `C(Y, Alb)` are spin factors). Incomparable, intrinsic, and exactly what is used.

**Route (claimed).** `V_W` non-zero purely exceptional. `pe_exists_exch_pair`: `p ⊥ q`
non-zero, `Q_s p = q`, `s² = 1` in `V_W`; `f := p + q`. In `V := V_{W⊗W}` (REC 134, `fam_tens`
orthogonality): `p⊗p, p⊗q, q⊗p, q⊗q` are pairwise exchangeable (`s⊗1`, `1⊗s`, `s⊗s`),
orthogonal, sum `f⊗f ≠ 0` (`tens_ne_zero`). Let `c₀ := centralCover (f⊗f)`
(`exists_central_cover`) and apply `JBWExceptionalSummand` to the central summand `c₀V`.
* JW: `a ↦ c₀ (a ⊗ f)` is a Jordan hom `V_W → c₀V` (`a⊗f = U_{1⊗f}(a⊗1)`, multiplicative by
  `mul_hom_of_Ph` + `rec126`; `c₀·` central), with `1 ↦ c₀(1⊗f) ≥ c₀(f⊗f) = f⊗f ≠ 0`
  (`(1−f)⊗f ≥ 0`); a non-zero Jordan hom of `V_W` into a C*-algebra. Contradiction.
* central `c ≤ c₀`, `c ≠ 0`, `cV` purely exceptional: `c(f⊗f) = 0` would give `f⊗f ≤ 1−c`,
  so `c₀ ≤ 1−c`, `c ≤ c₀(1−c₀) = 0`. Hence `c(f⊗f) ≠ 0`, and by all-or-none (exchange by
  `U_{c(s⊗1)+…}`) the four `c(p⊗p), …` are non-zero pairwise exchangeable orthogonal
  idempotents of the purely exceptional `cV` — contradicting `ExceptionalNoFourExch`.
This uses the *weak* Prop `JBWExceptionalSummand` (no "the rest is JW"); the central cover
replaces that. No Albert, no three factors, no frames summing to `1`, no bounded-rank ideal.
Estimate: 250–400 lines of glue (central summand as a JBW-algebra: `CentralIdem.Corner`,
transport of symmetries). Also sufficient in place of (b2), by Lemma A: `ExceptionalRankSplit`
— for every idempotent `p` some central `z` has `zp` and `(1−z)(1−p)` abelian (rank ≤ 3 form);
run it on a non-central idempotent of the weak closure of `S₁` in the exceptional summand.

## 4. (c) Why (a) fails: the exact obstruction

* What the infrastructure yields about a purely exceptional `V`: non-associativity of every
  central summand, an exchangeable pair `p ⊥ q` below `f = p + q`, and its corner `fVf` with a
  2-frame. In the model `C(Y, Alb)` these `p, q` have rank 1 and `fVf` is a spin factor —
  **special**. No contradiction can be extracted from a corner that is special in the model;
  the contradiction needs rank 3 (a frame summing to `1`, Shultz (i)) or the rank *bound*.
* Tensoring multiplies exchangeable families (`2^k` in `V_{W^{⊗k}}`, sum `f^{⊗k}`), and §3's
  dichotomy shows the only surviving case is "many exchangeable idempotents in a purely
  exceptional JBW-algebra". Ruling that out is `ExceptionalNoFourExch`, i.e. the
  `I_n (n ≥ 4), I_∞, II, III ⟹ JW` half of H-O–S 7.2.7: type decomposition (comparison,
  halving; 1,500–3,000 lines per `rec136-composites.md`) plus A–S 4.4 (coordinatization,
  >3,000 lines). The tensor gives no shortcut: op-commuting copies produce more exchangeable
  idempotents, never fewer, and REC's composite is not locally tomographic, so the
  Hanche-Olsen/BGW "no Jordan product on `Alb ⊗ Alb`" arguments do not apply.
* Identity route (angle 2): purely exceptional gives no Glennie-type positive information;
  "JB-algebra satisfying `G₈` is special" is not a theorem in H-O–S, and the subalgebra
  generated by op-commuting copies is not determined by REC's data. Dead end.
* Factor route (angle 3): weakly closed ideals are central cuts, minimal central idempotents
  need not exist; norm-closed factor quotients need the enveloping JBW-algebra (biduals, not
  in the tree), and "purely exceptional JBW factor ⟹ `Alb`" is the `n = 3` coordinatization.
  Dead end at the same depth as Shultz.

## 5. Recommendation

Keep `rec136_native_hypfree` as is; add (b2) as the intrinsic alternative
(`JBWExceptionalSummand + ExceptionalNoFourExch ⟹ rec136`, §3), since it is the first
statement that names exactly the missing piece and uses the new JBW infrastructure
(`pe_exists_exch_pair`, `exists_central_cover`) rather than an external target. Add (b1) only
if the author wants to drop the Albert algebra from the *statement* of the hypothesis: it is
strictly weaker than `ExceptionalAlbertMap` and its Lean proof is simpler than
`alb_threeway_nogo`, but needs `D`-fold tensors and (to derive it from the Albert map) a
`JBWAlgebra Alb` instance.

## Review (2026-09-26)

Adversarial review; no Lean, nothing compiled. Author's `r136na-descent.py` re-run: passes.

**Lemma A (§1): STANDS.** Op-commutation at the vector `p` gives `p(yp) = yp`, so `yp ∈ V₁(p)`
and `Ph p y = 0`; `mul_hom_of_Ph` makes `U_p ∘ φ` multiplicative, unital onto `p ≠ 0`.
`ECorner` is JBW (JBWProj:2296); an associative corner gives the Gelfand hom exactly as in
`centralIdem_not_assoc` (`C(charSet _, ℂ)`, same universe as `V'`, so `IsPurelyExceptional.{v,v}`
applies). Only op-commutation *evaluated at `p`* is used. The "useful converse" is unused.

**(b1) Prop as written: BROKEN (fixable).** `Module.finrank ℝ Q ≤ D` is vacuous for
infinite-dimensional `Q` (Mathlib `finrank = 0`). Take `Q := V` (infinite-dimensional for
`C(X, Alb)` with infinite `X`), `χ := id`: the Prop is satisfied without content and Lemma B
fails. State `FiniteDimensional ℝ Q ∧ finrank ℝ Q ≤ D` (or `χ : V → Fin D → ℝ` with JBW image).
**Lemma B, with that fix: STANDS, but the hypothesis does not match the glue.**
* The glue supplies op-commutation only on `χ(cV)`, not on `Q` (`χ` need not be onto, and
  `χ 1` need not be `1_Q`). The proof only ever evaluates op-commutation at vectors that are
  idempotents `p_j ∈ S_j` or lie in compressed images, so restate Lemma B with the ambient
  `A := χ(cV)` (a finite-dimensional Jordan subalgebra, unit `χ 1`) and corners `U_p A`.
* This needs `p_j ∈ S_j` (not merely in `Q`). `exists_nontrivial_idem` returns the range
  projection of `g(a)`, `g = max(· − mid, 0)`; the note's "norm closure of polynomials, finite
  dimension makes sups norm limits" is an unproved lemma. Cleaner: `jbCfc` embeds
  `C(sp a) ↪ Q`, so `sp a` is finite in finite dimension, and `p_j := jbCfc a 1_{t>mid}`
  directly; still needs `jbCfc a h ∈` any closed subalgebra containing `a` (check JBCalculus;
  if absent, ~100 lines). Est. 350–500 lines looks low with this; say 450–650.
* Op-commutation descent (`y w = y₁ w` for `w ∈ V₁`, `y ∈ V₁ ⊕ V₀`): correct. Unit of `Q_{j−1}`
  ∉ `Q_j` since `p_j ≠ 1`, so `finrank` drops; a scalar copy gives a character, composed
  into `C(PUnit, ℂ)`. Termination and the bound `k ≤ D − 1`: correct.
* "Strictly weaker than `ExceptionalAlbertMap`": only "implied by" is provable (both are true
  by Shultz); drop "strictly". The `JBWAlgebra Alb` instance is indeed absent (grep: no
  `OrderUnitSpace`/`JBAlgebra Alb`); `Papers/EJA/Appendix2.lean:1265` has `paperOUS` for a
  finite-dimensional EJA, which may make the 200-line estimate plausible (UNCLEAR).

**(b2) route: STANDS.**
* `a ↦ a ⊗ f`: `rec128_general` gives `Q_{1⊗f}(a⊗1) = a ⊗ f² = a ⊗ f` directly; `rec126`
  gives `Ph (1⊗f) (a⊗1) = 0`, so `mul_hom_of_Ph` + `rec127` make it Jordan. `x ↦ c₀x` is a
  Jordan hom for central idempotent `c₀` (`(c₀x)(c₀y) = c₀(x(c₀y)) = c₀(xy)`). Unit:
  `c₀(1⊗f) ≥ c₀(f⊗f) = f⊗f ≠ 0` (`(1−f)⊗f ≥ 0`, `U_{c₀}` positive). JW gives an injective
  (hence non-zero) hom into a vN algebra in `Type v`. Correct.
* `s⊗s` is a symmetry and `Q_{s⊗s}(p⊗p) = q⊗q`, both by `rec128_general` (+`rec127`); all six
  pairs covered (`s⊗1`, `1⊗s`, `s⊗s`). `ExchangeableBySymmetry` is not transitive, so `s⊗s` is
  needed; the note has it.
* Exceptional case: `c(f⊗f) = 0 ⇒ c = 0` via the central cover: correct. All-or-none: `Q_s`
  fixes central `c` (`s(sc) = c s² = c`) and `Q_s(cx) = cQ_s x`: correct. The corner-of-corner
  (`c` inside `c₀V`) is central in `V`: correct.
* **Is `ExceptionalNoFourExch` true? Yes.** The two-point attack fails: exchangeable
  idempotents have the *same central cover* (`Q_s` fixes central idempotents), so in
  `C(X, Alb)` the four supports coincide and at any point of them one would get four
  non-zero orthogonal idempotents of `Alb` (trace ≥ 4 > 3). With Shultz/H-O–S 7.2.7 the
  Prop holds. The "not implied by `ExceptionalAlbertMap`" remark is a formal-derivability
  observation (`χ` can kill the family), fine as stated.
* `ExceptionalRankSplit` checked pointwise on ranks 0–3 of `p` in `C(X, Alb)`: true.

**§4 "(a) not achievable": overclaimed.** It is a heuristic (the model `C(Y, Alb)` shows the
*listed* lemmas only reach special corners), not an independence proof: no model is given in
which all proved infrastructure holds and REC 136 fails. Reword as "no route found; every
route tried reduces to a rank bound". "Exact obstruction" likewise.

**Verdicts.** Lemma A STANDS. (b1) Prop BROKEN as written (finrank vacuity), Lemma B STANDS
after adding `FiniteDimensional` and re-basing on `χ(cV)` with `p_j ∈ S_j`. (b2) STANDS
(Prop true, glue checked against `rec126/127/128_general`). §4 UNCLEAR/overclaimed.
