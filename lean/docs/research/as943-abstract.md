# Is `AlfsenShultzJordanFromDerivations` true?  (9.43 without chain density)

Research note, 2026-09-26.  No Lean edits.  Inputs: Reconstruction.lean:2311–2360 (the
Prop, `ChainDense`), as943-transplant.md (+Review), JordanSymmetry.lean (`jordan_symmetry`,
`lemmaP`, `IsOrderDerivation.lie`), JordanFromChains.lean (`jb_of_chainDense`).
Numerics: scratch `abs943-g2.py` (Sym_4, genuine compressions).  **Everything is claimed.**

Notation as in as943-transplant: `D_i = U_i − U_{ci}`, `R_i = 1 − U_i − U_{ci}`,
`T_i = ½(1 + D_i)`, `p ⊥ q` iff `e_p + e_q ≤ 1`, `p' := c p`.

## 0. Verdict

* **(G2) is provable abstractly** from the Prop's hypotheses (§1, ~10 lines of math):
  for `p ⊥ q`, `U_{p'} U_{q'} = U_{q'} U_{p'}`; equivalently, for `e_j ≤ e_i`,
  `U_i U_{cj} = U_{cj} U_i`; equivalently `[D_p, D_q] = 0`.  Uses positivity, the closed
  form of `e^{tD_p}`, and the **kernel condition** (so the kernel condition is not idle).
  Consequence: the commutation clause of `ChainDense` is redundant (can be dropped from
  `ChainDense` / `jb_of_chainDense`, and from `va_chainDense`'s obligations).
* **(G1) is not a consequence of the hypotheses**, even when the conclusion holds (§2):
  in `M_2(ℝ)_sa` the family `{0, 1, p, p', q, q'}` (p, q rank one, non-commuting)
  satisfies every hypothesis of the Prop, its span is all of `W`, but chain combinations
  are not dense.  So `jb_of_chainDense` **cannot** prove the Prop in general; any proof
  needs a different route.
* **No counterexample found.**  In finite dimension any counterexample needs a
  non-symmetric cone (§3: on a symmetric cone the hypotheses force `U_i` to be the Jordan
  compressions, and then the conclusion holds with the Jordan product).  Polyhedral
  non-simplicial cones, ℓ^p-cones (p ≠ 2) and the Vinberg cone admit no spanning
  family (§3).  Truth of the Prop remains **open**; §4 states the exact remaining lemma.
* Recommendation: record the Prop as "open; G2 proved; G1 not implied"; keep it unused.
  Optionally simplify `ChainDense` by deleting its commutation clause (cheap, §1 in Lean
  ≈ 60–100 lines, reusing the O1–O3 lemmas already in JordanFromChains).

## 1. (G2) from the hypotheses (claimed)

Let `p ⊥ q`, `A := U_{p'}`, `B := U_{q'}`.  Available (O1–O3, as943-transplant §1,
Review: STANDS; they are proved in JordanFromChains): `U_p U_{q'} = U_p`,
`U_{q'} U_p = U_p`, `U_{p'} U_p = 0` (c is an involution), `e^{tD_p} = e^t U_p +
e^{−t} U_{p'} + R_p` is positive for all `t`.

**Step 1: `ABA = BA`.**  Let `v ≥ 0`, `w := Av ≥ 0`.  Then `U_p w = U_p U_{p'} v = 0`.
`Bw ≥ 0` and `U_p(Bw) = (U_p U_{q'}) w = U_p w = 0`.  Kernel condition for `p`
(`x ≥ 0`, `U_p x = 0 ⇒ U_{p'} x = x`) gives `A B w = B w`, i.e. `ABAv = BAv`.
Positives span `W`, so `ABA = BA`.

**Step 2: `ABA = AB`,** i.e. `AB(1 − A) = AB(U_p + R_p) = 0`.
(a) `A B U_p = U_{p'} (U_{q'} U_p) = U_{p'} U_p = 0`.
(b) `Φ := AB` is positive and `Φ U_p = 0` by (a).  For `w ≥ 0`:
`0 ≤ Φ e^{tD_p} w = e^{−t} Φ U_{p'} w + Φ R_p w`; let `t → ∞` (closed cone):
`Φ R_p w ≥ 0`.  So `Φ R_p` is positive, and `Φ R_p 1 = Φ(1 − e_p − e_{p'}) = 0`;
a positive map killing `1` is `0` (`−‖v‖1 ≤ v ≤ ‖v‖1`).  Hence `A B R_p = 0`.
(Same trick as O3.)

**Conclusion:** `AB = ABA = BA`.  With `p := j`, `q := ci` (`e_j ≤ e_i ⇔ j ⊥ ci`):
`U_{cj} U_i = U_i U_{cj}` — this is (G2).  With the O-lemmas all of `U_p, U_{p'}, U_q,
U_{q'}` then commute pairwise, so `[D_p, D_q] = 0`, `[T_p, T_q] = 0` for all nested or
orthogonal pairs.  (The as943-transplant attempt looked at `[R_p,R_q]` as an order
derivation killing 1, which is indeed not enough by itself; the kernel condition is the
extra input.)  Hypotheses used: positivity of `U`'s, `U_i1 = e_i`, `U_iU_{ci} = 0`,
injectivity (for `c` involutive), the kernel condition for `p` only, `D_p` an order
derivation (closed form of `e^{tD_p}`), Archimedean closed cone.  Not used: density,
directed completeness, `D_q` an order derivation beyond O3, Banach (only for O3's
`e^{tD}` which already needs it).
Numerics (Sym_4, `U_x y = xyx`, rank-1 `p` ⊥ rank-2 `q`): `ABR_p`, `ABA − BA`, `[A,B]`
all ≤ 2e−16; for non-orthogonal `p, q` the commutator is 0.43 (so ⊥ is needed).

**Lean shape.**  A lemma `compat_of_perp` (p ⊥ q ⇒ `U (c p) ∘ₗ U (c q) = U (c q) ∘ₗ U
(c p)`) next to O1–O3 in JordanFromChains; then `ChainDense` can drop the clause
`∀ k k', U (j k) ∘ₗ U (c (j k')) = …` (derive it from nesting inside `jb_of_chainDense`).
Estimate 60–100 lines + minor edits to `va_chainDense` (the clause just goes away).

## 2. (G1) is not implied (claimed; elementary)

`W = M_2(ℝ)_sa` (spin factor, Lorentz cone in ℝ³), `p = |0⟩⟨0|`, `q = |+⟩⟨+|`.  Family
`ι = {0, 1, p, p', q, q'}` with `c` the complement and `U_x y = xyx` (genuine Jordan
compressions; `U_0 = 0`, `U_1 = id`).  All hypotheses hold (W is a JB-algebra, finite-dim
⇒ directed complete; the genuine `U_p − U_{p'} = 2L(p) − 1` is an order derivation;
kernel condition = Peirce).  `span{1, p, q} = W` (3-dim).  Chains are nested lists from
the family; `p, q` are neither comparable nor orthogonal, so every chain combination lies
in `span{1,p} ∪ span{1,q}`: two planes, not dense.  The Prop's conclusion **holds**
(Jordan product).  So "span-dense ⇒ chain-dense" is false; the transplant route through
`jb_of_chainDense` can at best prove the Prop for families that happen to be chain dense.

Consequence for strategy: a proof of the Prop must either (R1) *enlarge* the family to a
chain-dense one (construct new compressions = spectral projections of arbitrary `a`,
with `U − U'` order derivations — essentially the whole of A–S spectral theory, where
directed completeness might be the input), or (R2) prove the Jordan identity and
`‖T_a‖ ≤ C‖a‖` for `T_a := Σ λ_k T_{i_k}` (well defined on the span, as943-transplant §2)
without spectral resolutions.

## 3. Where a counterexample could live (claimed; sketches)

A counterexample needs `W` **not order-isomorphic to a JB-algebra** (argued for finite
dimension below; in infinite dimension it needs the claim "order derivations of a JB-
algebra with `D1 = 2e − 1`, spectrum ⊆ {−1,0,1} and positive eigenprojections are
`2L(e) − 1`", believed but unchecked).

* **Symmetric cones are rigid.**  `g(K) = L(J) ⊕ Der(J)` is reductive; a real-
  diagonalisable `D ∈ g(K)` is `G°`-conjugate into `L(J)`: `D = g L(a) g^{-1}`.  Spectrum
  `⊆ {−1,0,1}` forces `a = 2p − 1` (L(a)'s eigenvalues are `(λ_j + λ_k)/2`).  `R u = 0`
  forces `y := g^{-1}u` to operator-commute with `p`; writing `g = k P(y^{−1/2})` with
  `k ∈ Aut(J)`, `P(y^{−1/2})` commutes with `L(p)`, so `D = L(2k(p) − 1)`: Jordan.  Hence
  every valid family on a symmetric cone is a family of projections with their Jordan
  compressions, and the conclusion holds with the Jordan product.
* **Finite-dim non-symmetric cones need `dim ≥ 5`-ish and a big `g(K)`**: the span of
  the `e_i` is `W`, `T_a ∈ g(K)` (sums of order derivations, `ExpIn.add`) and `T_a u = a`,
  so the orbit `G°u` is open.  Cones with small `g(K)` die: polyhedral non-simplicial
  (identity component = scalars ⇒ only `e ∈ {0,1}`), ℓ^p-cones p ≠ 2 (same), power cones
  (orbit of `u` 2-dim in ℝ³).  Homogeneous cones of dim ≤ 4 are symmetric (not claimed:
  that open orbit ⇒ homogeneous; Vinberg: smallest non-self-dual homogeneous cone is 5-dim).
* **Vinberg cone** `K = PSD ∩ {X ∈ Sym_3 : X_23 = 0}`, `g(K)` = `X ↦ AX + XAᵀ`, `A` upper
  with full first row (5-dim, solvable).  Valid `D` with `u = I`: diagonal
  `A = diag(±½, ±½, ±½)` give compressions onto `diag(1,1,0)`, `diag(1,0,1)`,
  `diag(1,0,0)` etc.; conjugates `gDg^{-1}` need `R g^{-1}I = 0`, which forces `g` to
  commute with `D` (checked by hand for the three types).  So all `e_i` are diagonal:
  **no spanning family**.  (Consistent with the forced product `L(a)u = a`,
  `L(a) ∈ g(K)` being the non-commutative clan product.)
* Infinite-dim ℓ^∞/c_0-sums of finite-dim pieces inherit JB-ness; `C(X)`-type spaces
  have only multiplication order derivations (norm-continuous weighted composition
  groups have trivial flow).  No candidate survives.

## 4. The precise remaining lemma (claimed reduction)

With G2 proved and as943-transplant §2 (well-definedness from symmetry + density):
the Prop is **equivalent** to

> **(L)** For the Prop's hypotheses, `T : span{e_i} → B(W)`, `T_{Σλ_k e_{i_k}} :=
> Σ λ_k T_{i_k}`, satisfies (i) `‖T_a‖ ≤ C‖a‖` for some `C`, (ii) the Jordan identity
> `T_{a²} T_a = T_a T_{a²}` on span (`a² := T_a a`), and (iii) `−1 ≤ a ≤ 1 ⇒
> 0 ≤ T_a a ≤ 1` on span.

(⇐: extend as in as943-transplant §3–§6 with the span in place of chains, using (i) for
the extension and continuity for (ii),(iii).  ⇒: a JBAlgebra product is bounded
(`sq_mem` + polarisation) and agrees with `T` on the span.)  In finite dimension (i) is
automatic and (L) says: a commutative unital algebra on a regular cone with all
`L(a) ∈ g(K)`, generated linearly by Peirce-type `e_i` (L(e_i) with spectrum ⊆ {0,½,1},
positive eigenprojections, kernel condition, pairwise compatibility G2 on ⊥/≤ pairs), is
Euclidean Jordan.  I know no theorem giving this without self-duality; a proof would
likely show `K` self-dual via an invariant trace form `τ(a∘b)` — not attempted.

## 5. Claimed, for adversarial review

1. G2 (§1): Step 1 via kernel condition, Step 2 via the O3 trick; hence `ChainDense`'s
   commutation clause is derivable from nesting.
2. §2 example: all hypotheses hold, span = W, chains not dense; so `jb_of_chainDense`
   cannot prove the Prop in general.
3. §3 symmetric-cone rigidity (standard Lie theory: hyperbolic elements of a reductive
   `g` are conjugate into `p`; stabiliser of `u` = `Aut(J)`).
4. §3 Vinberg cone: no spanning family (hand computation; not numerically searched).
5. §4 equivalence of the Prop with (L).
6. Not claimed: truth or falsity of the Prop.

## Review (2026-09-26)

Adversarial review; no Lean edits.  Scratch: `revabs-g2.py`, `revabs-vin.py`,
`revabs-vin2.py`.

1. **§1 (G2): STANDS.**  Checked line by line against the Prop / `Fam` hypotheses.
   Translation: `p := j`, `q := c i`; `e_j + e_{ci} ≤ 1 ⇔ e_j ≤ e_i` ✓; `B = U_{c(c i)} =
   U_i` needs `cc` (from injectivity, `Fam.cc`) ✓.  O-lemmas: `U_pU_{q'} = U_p` is `nD`,
   `U_{q'}U_p = U_p` is `nC`, `U_{p'}U_p = 0` is `hU (c j)` + `cc` ✓.  Step 1: `w = U_{cj}v
   ≥ 0`, `U_j(U_i w) = U_j w = 0` (nD), and the kernel condition is used in the direction
   `U_j x = 0 ⇒ U_{cj} x = x` for `x = U_i w ≥ 0` ✓; extension to all `v` is exactly
   `linext_nonneg` (OUS: every `v` is a difference of positives) ✓.  Step 2: `AB U_p =
   U_{cj}U_iU_j = U_{cj}U_j = 0` ✓; `Φ e^{tD_p} w = e^{−t}ΦU_{p'}w + ΦR_p w` (the `e^t`
   term dies), `t → +∞`, closed cone — the same limit as in `nD` ✓; `ΦR_p 1 = 0` then
   `pos_eq_zero` ✓.  So `U_iU_{cj} = U_{cj}U_i` for `e_j ≤ e_i`.  The other clauses of
   `ChainDense`'s commutation (k > k': `U_jU_{ci} = 0 = U_{ci}U_j` by nA/nB; k = k':
   `hU`) are already free, so the whole clause is derivable ✓.  `[D_i,D_j] = 0` for nested
   pairs also checks (the `U_{ci}`/`U_{cj}` pair is nC/nD applied to `e_{ci} ≤ e_{cj}`).
   Numerics (Sym_4, genuine compressions) agree, ~1e−16; non-⊥ pair 0.43.  (Genuine
   compressions commute anyway, so the numerics are only a sanity check; the abstract
   argument is what carries it.)  No non-Jordan counterexample attempted: none can exist
   since the proof is complete.
2. **§2: STANDS.**  All hypotheses verified by hand: `e` injective (0,1,p,1−p,q,1−q
   distinct), `U_0 = 0`, `U_1 = id` satisfy everything incl. the kernel clause
   (`D_0 = −id`, `D_1 = id` are order derivations); `U_p − U_{p'} = 2L(p) − 1`
   (Peirce), `e^{tD_p} = U_{e^{t/2}p + e^{−t/2}p'}` positive; kernel = Peirce.
   `span{1,p,q} = W` (dim 3).  Rank-one distinct `p, q, p', q'` are pairwise incomparable,
   so chains (repeats allowed) are ⊆ {1, x, 0}; with `l0` free, combinations lie in
   `span{1,p} ∪ span{1,q}`, two closed planes ✓.  `0, 1` are allowed but **not needed**:
   `{p,p',q,q'}` is also a counterexample (its span contains `1 = p + p'`).
3. **§3 symmetric-cone rigidity: STANDS as a sketch, with one misattributed step.**
   "Spectrum ⊆ {−1,0,1} forces `a = 2p − 1`" is false as stated (`a = 0`; or `J = ℝ²`,
   `a = (1,0)`).  What forces it is `R u = 0` (y := g⁻¹u interior, so `L(a)` has no
   0-eigencomponent on y ⇒ all `λ_j = ±1`); the note uses `R u = 0` one line later, so
   the fix is a reordering.  Cartan step (hyperbolic ⇒ conjugate into `p = L(J)`) and
   `g = k P(y^{−1/2})` are standard ✓.  Infinite-dim part: UNCLEAR (self-declared).
   Polyhedral claim "identity component = scalars" holds only for **indecomposable**
   cones (a direct sum of a ray and a square cone has 2-dim identity component and
   nontrivial compressions); harmless if one reduces to summands, but say so.
4. **§3 Vinberg: STANDS (numerically).**  `dim g(K) = 5` computed from supporting pairs
   (`revabs-vin2.py`), so the claimed 5-dim algebra is all of `g(K)`.  Search over
   `A` (diagonal ∈ {0,±½}, random first-row off-diagonals): every `D` with `D³ = D`,
   `R I = 0`, positive eigenprojections has zero off-diagonals, `e` diagonal; moreover
   e.g. `c(E11) = E22 + E33` fails the kernel clause.  No spanning family ✓.
5. **§4 equivalence: BROKEN as stated, repairable.**  (ii) writes `T_{a²}` with
   `a² = T_a a`, but `T_a a` need not lie in `span{e_i}` (`T_i e_j` for non-commuting
   `i,j`), so `T_{a²}` is undefined on the span.  Repair: first extend `T` using (i),
   then state (ii) as `T̄_{T̄_a a} T̄_a = T̄_a T̄_{T̄_a a}` for `a` in the span (or in `W`).
   With that, ⇐ (continuity + rescaled approximation for `sq_mem`) and ⇒ (JB product
   bounded, agrees with `T_i` via `e_i * w`) both go through; the equivalence is then
   close to a restatement of the Prop and adds little.
6. **Practical (drop `ChainDense`'s commutation clause): STANDS.**  `jb_of_chainDense`
   has `hker`, `hD`, `hU`, `hinj` inside `Fam`, which is all §1 uses; `nA`–`nD` +
   `expPos` + `pos_eq_zero` + `linext_nonneg` are in place, so 60–100 lines is realistic.
   Payoff is only simplification (`va_chainDense` already proves the clause).

**Verdict:** §1 STANDS, §2 STANDS, §3 STANDS (sketch; fix the `a = 2p−1` step and
"indecomposable"), Vinberg STANDS, §4 BROKEN as stated (ill-typed (ii); repairable),
practical claim STANDS.  Recommendation "open; G2 proved; G1 not implied" is sound.
