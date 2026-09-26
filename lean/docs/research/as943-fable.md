# `AlfsenShultzJordanFromDerivations`: TRUE in finite dimension (claimed), open in infinite

Research note, 2026-09-26 (Fable).  No Lean edits.  Inputs: Reconstruction.lean:2351 (the
Prop), as943-abstract.md (+Review), as943-transplant.md (+Review), as948-lemmaM.md (+Review),
JordanSymmetry.lean (`jordan_symmetry`, `lemmaP`, `IsOrderDerivation.lie`, `ExpIn.add`),
JordanFromChains.lean (`Fam`, `nA`–`nD`, `jb_of_chainDense`).  Numerics: scratch
`f943-hessian.py` (sanity checks of the calculus identities on Sym₂ and the Vinberg cone).
**Everything is claimed**, for adversarial review.  Notation as in as943-abstract:
`D_i = U_i − U_{ci}`, `T_i = ½(1 + D_i)`, `g(K)` = Lie algebra of `Aut(K)`.

## 0. Verdict

* **Finite dimension: the Prop holds** (§1–§3).  The proof does *not* go through chain
  density; it reformulates: the family gives a commutative unital product `∘` on `W` with
  every `L(a) ∈ g(K)`, and **any** such product on a proper cone forces `K` symmetric
  (Cartan decomposition of `g(K)` from the Hessian of the characteristic function, then
  compact stabilisers ⇒ homogeneity ⇒ self-duality) and `∘` = the Koecher–Vinberg Jordan
  product.  Uses: symmetry `T_i e_j = T_j e_i` (proved in Lean), `D_i` order derivations,
  span = W.  **Not used**: the kernel condition, directed completeness, positivity of the
  `U_i` beyond what symmetry needs, G2, chain density, the §3 rigidity lemma of
  as943-abstract (it becomes a corollary).
* **No counterexample**, in any dimension; the finite-dim theorem also kills every
  ℓ^∞-sum-of-finite-dim candidate (§4).
* **Infinite dimension: open.**  Every tool (characteristic function, compact stabilisers,
  Cartan conjugacy, Koecher–Vinberg) is finite-dimensional; the exact gap is §4.
* **REC is unaffected**: nothing uses the Prop (`rec121` is proved via `jb_of_chainDense`).
  The only consequence is documentary: the Prop's docstring/README should say "true in
  finite dimension (as943-fable), open in infinite dimension" instead of "open".

## 1. The product (claimed; abstract, any dimension, on the span)

Let `S := span{e_i}`.  For `a = Σλ_k e_{i_k}` put `L(a) := Σλ_k T_{i_k}`.  By the symmetry
`T_i e_j = T_j e_i` (`jordan_symmetry`) and density this is well defined (as943-transplant
§2, Review: STANDS) and `L(a)b = L(b)a` on `S × S`, `L(a)1 = a`, `L(1) = id`.  Each
`T_i = ½·1 + ½D_i` and `D_i` is an order derivation, so `L(a)` is an order derivation
(`ExpIn.add`, scalars): `exp(tL(a)) ∈ Aut(K)` for all `t`.  In finite dimension `S = W`
(a dense subspace is everything), so **`(W, ∘)` with `a∘b := L(a)b` is a commutative unital
bilinear product with `L(W) ⊆ g(K)`**.  Conversely the Prop's conclusion says exactly that
this `∘` is a Euclidean Jordan product whose cone of squares is `K` (a JB product is
determined by its values on the spanning `e_i`).  So in finite dimension the Prop is
equivalent to Theorem 2.

## 2. Theorem (claimed): commutative sections of `g(K)` are Jordan

> Let `K ⊂ W` (finite-dim) be a closed proper generating cone, `1 ∈ int K`, and `∘` a
> commutative bilinear product with `1∘a = a` and `L(a) := a∘· ∈ g(K)` for all `a`.  Then
> `K` is a symmetric cone and `∘` is the Koecher–Vinberg Euclidean Jordan product of
> `(W, K, 1)` (unit `1`, cone of squares `K`).

Proof.  Let `φ(x) = ∫_{K*} e^{−⟨x,ξ⟩}dξ` be the characteristic function (Faraut–Korányi
I.3), `f := log φ`: smooth, strictly convex on `int K`, `f(gx) = f(x) − log|det g|` for
`g ∈ Aut(K)`, and `−df(x) ∈ int K*`.  Put `ξ := −df(1)`, `τ := d²f(1)` (positive definite).

(a) *Derivative identities.*  For `X ∈ g(K)`: `f(exp(tX)x) = f(x) − t·tr X`; `∂_t` at 0
gives `df(x)[Xx] = −tr X` for all `x`; differentiating in `x` along `v`, then `w`, at `x = 1`:
  (1) `τ(X1, v) = ξ(Xv)`;  (2) `d³f(1)[X1, v, w] = −τ(Xw, v) − τ(Xv, w)`.
Let `h := {X ∈ g(K) : X1 = 0}` (stabiliser).  (1) with `X ∈ h`: `ξ∘X = 0`.  (2) with
`X ∈ h`: **`h ⊆ so(τ)`**.  (1) with `X = L(a)`: **`τ(a, v) = ξ(a∘v)`**.

(b) *`L(W) ⊆ Sym(τ)`.*  `[L(v), L(w)] ∈ g(K)` (Lie algebra) and `[L(v),L(w)]1 = v∘w − w∘v
= 0`, so `[L(v),L(w)] ∈ h` and `ξ(v∘(w∘a)) = ξ(w∘(v∘a))`.  Hence `τ(L(a)v, w) =
ξ(w∘(a∘v)) = ξ(v∘(a∘w)) = τ(v, L(a)w)` (commutativity used twice).

(c) *Cartan decomposition.*  `ev: g(K) → W`, `X ↦ X1` is onto (`L(a)1 = a`) with kernel
`h`, and `L` is a section, so `g(K) = L(W) ⊕ h` with `L(W) ⊆ Sym(τ)`, `h ⊆ so(τ)`.  Thus
`g(K)ᵀ = g(K)` (τ-transpose), so `g(K)` is reductive (self-adjoint linear Lie algebra),
`k := g(K) ∩ so(τ) = h` and `p := g(K) ∩ Sym(τ) = L(W)` (an element `L(a) + δ` that is
antisymmetric forces `L(a)` symmetric and antisymmetric, so `a = L(a)1 = 0`).  Also
`g(K^τ) = g(K)ᵀ = g(K)`, so `G := Aut(K)°` also preserves `K^τ := {y : τ(y, K) ≥ 0}`.

(d) *Polar decomposition.*  `G` is a closed connected linear group closed under
τ-transpose, so `G = K_c·exp(p)` with `K_c = G ∩ O(τ)` connected, `Lie(K_c) = h`, hence
`K_c ⊆ Stab(1)` (Knapp, *Lie groups beyond an introduction*, Prop. 1.143 / Thm. 1.143 style;
maximal compact subgroups of `G` are the conjugates of `K_c`).

(e) *Homogeneity.*  For `y ∈ int K` (or `int K^τ`; `1 ∈ int K^τ` since `τ(1,·) = ξ ∈ int K*`),
`Stab_G(y)` preserves the compact body `[−y, y]` with nonempty interior, so it is compact,
hence lies in a conjugate of `K_c`, so `dim Stab_G(y) ≤ dim h` and `dim(G·y) ≥ dim W`:
every orbit in `int K` and in `int K^τ` is open.  Both interiors are connected, so
`int K = G·1 = int K^τ`: **`K` is homogeneous and `K = K^τ` (self-dual), i.e. symmetric.**

(f) *`Stab(1) = K_c` and the product.*  If `k·exp(L(a))` fixes `1` with `k ∈ K_c` then
`exp(L(a))1 = 1`; `L(a)` is τ-symmetric hence diagonalisable with real spectrum, so
`exp(L(a)) − 1 = L(a)·(invertible)`, `L(a)1 = 0`, `a = 0`.  So `G_1 = K_c = G ∩ O(τ)`, and
Faraut–Korányi III.3.1 (Koecher–Vinberg) applies to `(W, τ, K, e := 1)`: the Euclidean
Jordan product is *defined* by `L_J(x) :=` the unique element of `p` with `L_J(x)1 = x`,
`x∘_J y := L_J(x)y`, and `K` is its cone of squares.  Since `p = L(W)` and `L(x)1 = x`,
`L_J = L`: `∘ = ∘_J`.  ∎

Corollaries.  (i) The Prop holds for finite-dimensional `W` (any `ι`, finite or not): the
`JBAlgebra` fields (Jordan identity, `−1 ≤ a ≤ 1 ⇒ 0 ≤ a² ≤ 1` in the given order,
which is the JB order as `K` = squares, Banach automatically) hold, and `e_i * w = T_i w`
by construction.  (ii) as943-abstract §3's rigidity ("valid families on symmetric cones
are Jordan compressions") is a corollary: `T_i = L_J(e_i)`, so `U_i = ` the `1`-eigen-
projection of `2L_J(e_i) − 1`, the Jordan compression.  (iii) A non-symmetric finite-dim
cone admits **no** commutative unital section of `g(K)` at all — matching the Vinberg-cone
finding (no spanning family): there `dim g(K) = dim W` and the forced clan section is
non-commutative.  (iv) In finite dimension chain density holds *a posteriori* (spectral
resolutions in `J`), never within the family (as943-abstract §2) — the two are consistent.

Numerics (`f943-hessian.py`, finite differences, residuals ≤ 2e−5): (1), (2) on Sym₂ with
`f = −(3/2)log det` for `X = L(a) + derivation`, and on the Vinberg cone with `f` from its
simply transitive triangular group; `h ⊆ so(τ)`, Jordan `L(a) ∈ Sym(τ)` on Sym₂; on the
Vinberg cone the clan section has `|τL − Lᵀτ| = 4.8` and `|L(a)b − L(b)a| = 1.2` — as (b)
predicts, non-commutativity is exactly what breaks τ-symmetry there.

## 3. Hypotheses actually consumed (finite dimension)

From the Prop: `IsOUS` (closed proper cone, order unit), `U_i` positive with `U_i1 = e_i`,
`U_i² = U_i`, `U_iU_{ci} = 0`, `e_{ci} = 1 − e_i`, injectivity (for `c` involutive) — all
only through `jordan_symmetry` — plus `D_i` order derivations and density (= span).
Idle in finite dimension: the kernel condition, `IsDirectedCompleteOUS`, `IsBanachOUS`.
(A–S 9.43 uses the kernel condition for G2; Theorem 2 never needs G2.)

## 4. Infinite dimension: the exact gap (claimed)

The Prop is equivalent (given §1) to: the bilinear map `L : S → B(W)` on the dense span
`S` extends to a JB product.  What Theorem 2 supplies is only the *shape* of a proof:
(i) **boundedness** `‖L(a)‖ ≤ C‖a‖` on `S` (in finite dimension it is automatic and
equals `C = 1` after the fact — the eigenvalues of `L_J(a)` are `(λ_j+λ_k)/2`);
(ii) with (i), `int K` is a real-analytic Banach manifold acted on by `G := ⟨exp L(W)⟩`;
one would need `G·1 = int K` and an infinite-dimensional Koecher–Vinberg (Upmeier,
*Symmetric Banach manifolds and Jordan C*-algebras*, symmetric cones ↔ JB-algebras
[unverified reference]).  Neither the characteristic function nor compactness of
stabilisers nor Cartan conjugacy exists in infinite dimension; I see no substitute.
What Theorem 2 *does* settle about candidates: an infinite-dim counterexample cannot be
built from finite-dim pieces.  In an `ℓ^∞`-sum `⊕ W_k` with a "product family"
`(e^{(k)}_{i_k})_k` (per-coordinate families containing `0, 1`; span dense; directed
complete), each `W_k` carries a spanning valid family, so is Euclidean Jordan by Theorem 2,
and the sum is JB.  `c_0`-sums with the union family are not directed complete
(`sup` of odd-indexed partial units fails), so the Prop's directed-completeness hypothesis
excludes them.  `C(X)` and `ℓ^p`-type cones were already excluded (as943-abstract §3).
So a counterexample, if any, is a genuinely infinite-dimensional non-JB Banach OUS with a
dense spanning family and unbounded `L` — no candidate known.  Verdict: open.

## 5. Claimed, for adversarial review

1. §1: in finite dimension the Prop ⟺ Theorem 2 (well-definedness from symmetry alone).
2. Theorem 2(a): identities (1), (2) from equivariance of `log φ`; `ξ ∈ int K*`, `τ ≻ 0`.
3. Theorem 2(b): commutativity ⇒ `L(W) ⊆ Sym(τ)` (via `[L(v),L(w)] ∈ h`, `ξ∘h = 0`).
4. Theorem 2(c)–(e): `g(K) = L(W) ⊕ h` is a Cartan decomposition; reductivity; polar
   decomposition of `Aut(K)°`; compact stabilisers ⇒ all interior orbits open ⇒ `K`
   homogeneous and `τ`-self-dual.
5. Theorem 2(f): `Stab(1) = K_c`; FK III.3.1 defines the Jordan product as the `p`-section,
   so it equals `∘`; cone of squares = `K`.
6. §3: the kernel condition, directed completeness, G2 are idle in finite dimension.
7. §4: `ℓ^∞`-sums of finite-dim pieces cannot be counterexamples; the gap is (i)+(ii).
8. Not claimed: truth or falsity in infinite dimension.  REC unaffected either way.

## Review (2026-09-26)

Adversarial review (Opus); no Lean.  Script: scratch `revf943-check.py`.  **Overall: the
finite-dimensional theorem STANDS**; one citation to fix, one scope overstatement in §4.

* **§1 / (a) `L(W) ⊆ g(K)`, well-definedness — STANDS.**  If `Σλ_k e_{i_k} = 0` then
  `(Σλ_k T_{i_k}) e_j = Σλ_k T_j e_{i_k} = T_j 0 = 0` for every `j` (symmetry), so
  `Σλ_k T_{i_k}` vanishes on the span `= W`: `L` is well defined.  `D_i` order derivation
  ⇒ `exp(tD_i)K = K` ⇒ `D_i ∈ g(K)`; `id ∈ g(K)` (dilations); `g(K)` (tangent algebra of
  the closed group `Aut K`) is a vector space, so `T_i`, `L(a) ∈ g(K)`.  `jordan_symmetry`
  (JordanSymmetry.lean:445) takes only `IsBanachOUS`, injectivity, `e_{ci}=1−e_i`, the
  `U`-axioms and `hD` (via `lemmaP`) — no kernel condition, no directed completeness —
  so §3's "idle" list is right.  `IsOUS` = norm + `cone_closed` in `ousNorm`; in finite
  dimension that is a closed proper cone with `1` interior, as §2 needs.
* **(a) identities (1), (2) — STANDS.**  Rederived: differentiate `df(x)[Xx] = −tr X` in
  `v` then `w`.  Numerically on the Lorentz cone `R⁴` (`f = −2 log(x₀²−|x|²)`,
  `g = R·1 ⊕ so(1,3)`) and on `Sym₃` (`f = −2 log det`, `g = gl₃` acting by `AxAᵀ`): (1)
  residual ≤ 2e−5; (2) residual → 0 as `O(h²)` under step refinement (0.59→0.009 and
  0.89→0.013); `h ⊆ so(τ)` exact.
* **(b) `L(W) ⊆ Sym(τ)` — STANDS.**  `[L(v),L(w)]1 = v∘w − w∘v = 0` ⇒ in `h` ⇒ `ξ∘[L(v),L(w)]
  = 0`; with `τ(x,y) = ξ(x∘y)` (from (1), `X = L(x)`, symmetric as a Hessian),
  `τ(a∘v,w) = ξ(w∘(v∘a)) = ξ(v∘(w∘a)) = τ(v,a∘w)`.  Checked: spin-factor / Jordan `L(a)`
  τ-symmetric to 1e−10.  Also `X = 1` in (1) gives `ξ = τ(1,·)`, used in (e).
* **(c) Cartan decomposition — STANDS.**  `X − L(X1) ∈ g(K)`, kills `1`, so in `h`;
  direct since `L(a) ∈ h ⇒ a = L(a)1 = 0`; `[L(W),L(W)] ⊆ h` as in (b); `g(K)` is
  τ-transpose closed; `k = h`, `p = L(W)` as claimed.
* **(d) polar decomposition — STANDS, CITATION WRONG.**  "closed + transpose-closed" alone
  does not give `G = K·exp p`: the discrete group `⟨diag(2,1,½)⟩` is closed and
  transpose-closed with `p = 0` (it is even `Aut` of a cone: the closed cone spanned by
  `(2ⁿ,1,2⁻ⁿ)`, which is not invariant under `diag(2ᵗ,1,2⁻ᵗ)`, `t ∉ ℤ` — the extreme
  rays of `{xz ≥ y²}` in between are missing).  So `Aut(K)` itself need not
  polar-decompose; the note correctly uses the *identity component*.  For connected
  `G` with reductive, transpose-closed `g`, cite semisimple part (Knapp, *Beyond*, Thm
  6.31) × centre (`exp z_k · exp z_p`), not "Prop. 1.143 style".  `K_c = G ∩ O(τ)` is
  compact (`G` closed), connected (`G ≅ K_c × p`), `Lie K_c = h`, so `K_c ⊆ Stab(1)`.
* **(e) homogeneity, self-duality — STANDS.**  Stabilisers compact (they preserve the
  order interval `[−y,y]`, resp. its `K^τ` analogue; `K^τ` proper since `K` generating;
  `1 ∈ int K^τ` since `τ(1,·) = ξ ∈ int K*`).  Compact ⊆ conjugate of `K_c`: Cartan fixed
  point on `G/K_c ≅ {ggᵀ}` (closed totally geodesic in `Sym⁺`, a Hadamard manifold;
  Euclidean factor from `R·1` harmless).  Dimension count and connectedness of the two
  interiors then give `int K = G·1 = int K^τ`.
* **(f) `G_1 = K_c`, FK III.3.1 — STANDS.**  `exp(L(a))1 = 1` with `L(a)` τ-symmetric ⇒
  `L(a)1 = 0` ⇒ `a = 0`.  FK's `L_J(x)` = the unique element of `p` with `L_J(x)e = x`;
  `p = L(W)` ⇒ `L_J = L`.  (Full `Aut(K)_1` also lies in `O(τ)`: it preserves `f`, hence
  `τ`, since `|det| = 1` on a compact group.)
* **Conclusion vs Lean `JBAlgebra` (Algebras.lean:263) — STANDS.**  Fields: comm, unit,
  Jordan identity, bilinearity, `−1 ≤ a ≤ 1 ⇒ 0 ≤ a² ≤ 1` *in the given order* (= squares
  order since `K` = cone of squares; spectrum argument), `banach` (finite dim).  No
  `‖ab‖ ≤ ‖a‖‖b‖` field is required.  `e_i * w = T_i w` by construction.
* **§4 — sums: OVERSTATED (not wrong in what it proves).**  The argument covers only
  *coordinatewise* ("product") families.  "An infinite-dim counterexample cannot be built
  from finite-dim pieces" should read "…from coordinatewise families on `ℓ^∞`-sums of
  finite-dim pieces"; families whose `U_i` mix summands are not addressed.  "`c_0`-sum"
  should be `c` / `c_0 ⊕ R1` (`c_0` has no order unit).  The infinite-dim gap description
  is fair: every tool used (char. function, compact stabilisers, Cartan conjugacy) is
  genuinely finite-dimensional.
* **§5 items 1–6: STANDS; 7: STANDS with the scope fix above; 8: agreed.**
  Suggested docstring wording: "true for finite-dimensional `W` (as943-fable, reviewed);
  open in infinite dimension".
