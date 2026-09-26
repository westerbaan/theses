# `AlfsenShultzJordanFromDerivations` in infinite dimension: a reduction (claimed)

Research note, 2026-09-26.  No Lean edits.  Inputs: Reconstruction.lean:2311, as943-fable,
-abstract, -transplant (+Reviews), JordanSymmetry/JordanFromChains.lean.  Scratch
`inf943-lietriple.py`.
**Everything is claimed**, for adversarial review.  Notation as before: `D_i = U_i − U_{ci}`,
`R_i = 1 − U_i − U_{ci}`, `T_i = ½(1 + D_i)`, `S = span{e_i}` (dense), `L : S → B(W)`,
`L(Σλ_k e_{i_k}) = Σλ_k T_{i_k}` (well defined, `L(a)b = L(b)a`, `L(a)1 = a`, every
`L(a)` an order derivation; as943-fable §1, Review: STANDS).

## 0. Verdict: (c), the precise remaining lemma

Not settled: no proof, no counterexample.  What is new:
* **(N)** The `U_i` are neutral, hence genuine Alfsen–Shultz compressions (§1).
* **(B)** Boundedness (i) holds as soon as *bounded-coefficient* combinations of the
  family are dense — much weaker than chain density (G1); and (i) is equivalent to a
  pointwise statement (§2).  The brief's angle "bound an order derivation by its value
  at 1" is false on OUSs, even on JB-algebras (§2).
* **(H)** Given (i), `int K` is a single orbit of `G := ⟨exp L(W)⟩` — homogeneity with
  **no compactness**, via the Thompson metric (§3).  So the finite-dim tool (e) is
  replaced; what is still missing is the substitute for the *trace form* `τ` (steps
  (b), (f) of as943-fable Theorem 2).
* **Remaining lemma** (§4): with (i), the extended bounded commutative product `∘`
  satisfies (J) the Jordan identity and (P) `−1 ≤ a ≤ 1 ⇒ 0 ≤ a∘a ≤ 1`.  Prop ⟺ (i)+(J)+(P).
* Angle 2 (finite-dim reduction) fails structurally (§5); a counterexample needs
  unbounded `L`, or bounded `L` on a homogeneous non-JB cone (§6).

## 1. (N) Neutrality; the `U_i` are A–S compressions (claimed; elementary)

Let `ω` be a state with `ω(e_i) = 1`.  Then `ω(e_{ci}) = 0`, and for `w ≥ 0`,
`0 ≤ U_{ci}w ≤ ‖w‖e_{ci}`, so `ω∘U_{ci} = 0`.  From `e^{tD_i} = e^tU_i + e^{−t}U_{ci} + R_i`
(O3's closed form) positive: `e^tω(U_iw) + ω(R_iw) ≥ 0` for all `t`; `t → −∞` gives
`ω∘R_i ≥ 0`, and `ω(R_i1) = ω(1 − e_i − e_{ci}) = 0`, so `ω∘R_i = 0` (positive functional
vanishing at 1).  Hence **`ω(e_i) = 1 ⇒ ω∘U_i = ω`** (neutral).  Consequences:
* primal complements: `ker⁺U_i = im⁺U_{ci}` is the kernel hypothesis, and `im⁺U_i =
  ker⁺U_{ci}` is the kernel hypothesis for `ci` (`c` involutive);
* dual complements: for `φ ≥ 0`, `φ∘U_i = 0 ⇔ φ∘U_{ci} = φ` (⇐: `U_{ci}U_i = 0`; ⇒:
  `φ(e_i) = 0`, apply neutrality for `ci` to `φ/φ(1)`); `‖U_i‖ ≤ 1`.
So each `U_i` is a *bicomplementary normalised positive projection*, i.e. a compression
in the sense of A–S (*State spaces*, Ch. 7) [definition recalled, unverified], and `e_i`
a projective unit.  (A–S: a compression is determined by its projective unit
[unverified]; if so, the `U_i` are determined by the set `{e_i}`.)  What A–S additionally
have and the Prop lacks: compressions for *all* projective faces / spectral duality —
i.e. spectral resolutions, which is exactly the missing (G1).

## 2. (B) Boundedness (claimed)

* `‖T_i‖ ≤ 1` (`‖D_i‖ ≤ 1`, as943-transplant §1), hence **`‖L(a)e_j‖ = ‖T_ja‖ ≤ ‖a‖`**.
* Let `ℓ¹(b) := inf{Σ|μ_j| : b = Σμ_j e_j}` and `D_C := {b ∈ S : ℓ¹(b) ≤ C‖b‖}`.
  **If `D_C` is norm dense in `W` for some `C`, then `‖L(a)‖ ≤ C‖a‖` on `S`.**  Proof: for
  `b ∈ D_C`, `‖L(a)b‖ = ‖L(b)a‖ ≤ Σ|μ_j|‖T_ja‖ ≤ C‖b‖‖a‖`; `L(a)` is bounded (finite sum),
  so the bound passes to the closure of `D_C`.  Chain combinations lie in `D_4`
  (layer bounds, `1 = e_i + e_{ci}`), so this generalises the chain step of
  `jb_of_chainDense`; in the as943-abstract §2 example (`span{1,p,q} = M₂(ℝ)_sa`) `D_C`
  is dense (finite dim) although chains are not.
* **(i) ⟺ pointwise boundedness**: `sup{‖L(a)w‖ : a ∈ S, ‖a‖ ≤ 1} < ∞` for every
  `w ∈ W` (⇐ Banach–Steinhaus; it already holds on `S`, as `‖L(a)b‖ ≤ ‖L(b)‖‖a‖`, but
  `S` is meagre in general, so this is not automatic).
* **The brief's angle 1 fails as posed.**  On an OUS an order derivation is not bounded
  by its value at 1, even on a JB-algebra: in the spin factor `ℝ⊕ℝ²` (= `M₂(ℝ)_sa`),
  `δ_θ := L(a) + θ·ρ` with `ρ` the rotation generator of `ℝ²` (a derivation, `ρ1 = 0`)
  is an order derivation with `δ_θ1 = a` and `‖δ_θ‖ → ∞`.  Also `L(1+a)` is not positive
  for `a ≥ −1` (Peirce-½ parts), so no order sandwich for `L(a)` exists.  Any bound
  must use that `L(a)` is the "`p`-part" (a sum of `T_i`'s).

## 3. (H) Given (i), `K` is homogeneous (claimed)

Assume (i) and extend `L` to `W` (`‖L(a)‖ ≤ C‖a‖`).  For `a ∈ W`, `L(a_n) → L(a)` in
operator norm (`a_n ∈ S`), so `e^{±L(a)}` are norm limits of order automorphisms:
**`e^{L(a)} ∈ Aut(K)` for all `a ∈ W`.**  Let `G := ⟨e^{L(a)} : a ∈ W⟩`.
1. `F(a) := e^{L(a)}1` is analytic `W → W` with `dF(0) = id` (`L(h)1 = h`); by the
   Banach inverse function theorem `F` maps a neighbourhood of 0 onto a neighbourhood
   `N` of 1; `N ⊆ G·1`.  For `y = g1`, `gN` is a neighbourhood of `y`: `G·1` is open.
2. Thompson metric `d_T(x,y) = log max(M(x/y), M(y/x))` on `int K`: it induces the
   norm topology there (Thompson 1963, normal cones; OUS cones are normal) and every
   linear order automorphism is a `d_T`-isometry.  If `g_n1 → y ∈ int K`, then
   `d_T(1, g_n⁻¹y) = d_T(g_n1, y) → 0`, so `g_n⁻¹y ∈ N` eventually and `y ∈ G·1`:
   `G·1` is closed in `int K`.
3. `int K` is convex, so connected: **`int K = G·1`**; `K = closure(G·1)`.
Corollaries: (a) given (i) the cone is determined by the family: if the `T_i` are the
multiplications of *some* JB structure on the same Banach space, `K` is its cone.
(b) Homogeneity needs no compact stabiliser (as943-fable used compactness for (e), (f)).

## 4. The remaining lemma (claimed equivalence)

> **Prop ⟺ (i) + (J) + (P)**, where, with `a∘b := L̄(a)b` the bounded extension,
> (J) `[L̄(a), L̄(a∘a)] = 0` for all `a ∈ W`, (P) `−1 ≤ a ≤ 1 ⇒ 0 ≤ a∘a ≤ 1`.

(⇐: `JBAlgebra` fields by continuity + (J), (P); `e_i∘w = T_iw` by construction.
⇒: a JB product has `‖L(a)‖ ≤ ‖a‖` and agrees with `L` on `S`.)  This repairs as943-abstract §4 (Review item 5: `T_{a²}`
ill-typed on `S`) — (J), (P) are stated after extension.  By §2, (i) may be replaced by
"`D_C` dense for some `C`", after which only (J), (P) remain.

**What would give (J), and why the finite-dim proof does not.**  With (i), `g(K) ⊇
L(W) ⊕ h`, `h` = unital order derivations (generators of unital order automorphisms =
unital isometries), and `[L(v), L(w)] ∈ h` (it kills 1).  The finite-dim proof gets
`[h, L(W)] ⊆ L(W)` — equivalently (K): *every `X ∈ h` of the form `[L(v),L(w)]` is a
derivation of `∘`* — from the `h`-invariant trace form `τ(a,b) = ξ(a∘b)`.  In infinite
dimension no such form exists even in the true case (`B(H)_sa` has no finite trace), so
any proof of (J) must be **non-tracial**.  (K) is at least very close to (J): numerically
(`inf943-lietriple.py`, Levenberg–Marquardt on structure constants, dim 4, unital
commutative), 60/60 solutions of "[L_a,L_b] is a derivation ∀a,b" were Jordan (max
violation < 1e−6 tested); the implication (K) ⇒ (J) is **not proved** (commutative
algebras with `[L_a,L_b] ∈ Der` — Lie triple algebras [unverified name] — need not be
Jordan without a unit; unital case unknown to me).
**Literature route** [unverified references]: infinite-dim Koecher–Vinberg — Chu, *J.
Algebra* 491 (2017); Lemmens–Roelands–Wortel (Thompson-metric symmetric cones ⇔
JB-algebras).  These need, beyond homogeneity (§3), a **symmetry at 1** (an involutive
`d_T`-isometry of `int K` with isolated fixed point 1).  The candidate
`s(e^{L(a)}1) := e^{−L(a)}1` is an isometry iff `d_T(1, e^{−L(a)}e^{L(b)}1) =
d_T(1, e^{L(a)}e^{−L(b)}1)` — in a JB-algebra this is `(P(y)z)⁻¹ = P(y⁻¹)z⁻¹` (Hua
type), i.e. (J)-strength.  So the literature route reduces to the same gap.
**Commuting special case**: if all `U_i` commute pairwise, all `L(c)` (`c ∈ S`) commute;
given (i), `L̄(a∘b)c = L(c)L(a)b = L(a)L(b)c` for `a,b,c ∈ S`, so `L̄(a∘b) = L̄(a)L̄(b)`:
`∘` is associative and (J) holds.  ((i) itself is not shown in this case.)

## 5. Angle 2 (finite-dimensional reduction) fails (claimed)

(a) Invariant subspaces generated by finitely many members need not be finite-dim: two
projections `p, q` in general position in `B(ℓ²)` generate (Jordan compressions,
`L(p), L(q)` applied to 1) an infinite-dim JB-algebra ≅ `C(σ, M₂)`-type; three
projections can generate all of `B(H)_sa` weakly.  So no finite-dim `U`-invariant
subspace containing `S_F := span{e_i : i ∈ F}` exists in general.  (b) Even the Jordan
identity for `a ∈ S_F` involves `L(a∘a)`, and `a∘a = Σλ_kλ_lT_ke_l ∉ S` in general, so
it is not a statement about `S_F` at all.

## 6. Angle 3: shape of a counterexample (claimed)

Any counterexample has one of: **(α)** `L` unbounded on `S` — then `D_C` is dense for no
`C`, the orbit map `a ↦ e^{L(a)}1` on `S` has no bounded derivative, and every `ℓ¹`
representation of some small elements has huge coefficients; or **(β)** `L` bounded,
`K` homogeneous (§3), `∘` commutative with `L(W) ⊆ g(K)`, but not Jordan — an
infinite-dim analogue of a non-symmetric homogeneous cone that nevertheless admits a
commutative section (impossible in finite dim, as943-fable Cor. (iii)).  Ruled out:
commutative `C(X)`-type (cone invariant under multiplication by positive simple
functions and containing the order unit ⇒ `K` = pointwise cone: rigid); spin-type
`ℝ⊕E` with `E` non-Hilbert (no boosts in `g(K)`, so no `L(a)` with `L(a)1 ∉ ℝ1`;
as943-abstract §3 in finite dim, same argument pointwise for `ℓ^p`); `ℓ^∞`-sums of
finite-dim pieces with coordinatewise families; "same space, smaller cone" deformations
of a JB-algebra with its projections as family and bounded `L` (§3 (a): `K` is forced).
No candidate for (α) or (β) found.

## 7. Claimed, for adversarial review

§1 neutrality ⇒ A–S compressions; §2 `D_C`-density ⇒ (i), (i) ⇔ pointwise bound, the
spin-factor non-bound; §3 (i) ⇒ `int K = G·1`; §4 Prop ⟺ (i)+(J)+(P), non-tracial
necessity, commuting case; §5–§6.  Not claimed: truth/falsity in infinite dim; (K) ⇒ (J).

## Review (2026-09-26)

Adversarial check against Reconstruction.lean:2311 and `JBAlgebra` (Algebras.lean:263).
Scratch: `revinf-nil.py`, `revinf-ex.py`.

**§1 (N): STANDS.**  `U_iU_{ci} = 0` and `c` is involutive (`e` injective, `e(c(ci)) = e_i`),
so `U_{ci}U_i = 0` as well.  Then `D² = U + U'`, and `e^{tD} = R + e^tU + e^{−t}U'` is exact.
Positivity of `e^{tD_i}` follows from `IsOrderDerivation`.  For `ω(e_i) = 1` and `w ≥ 0`:
`ω∘U_{ci} = 0`, so `e^tω(U_iw) + ω(R_iw) ≥ 0`.  Letting `t → −∞` kills the `U_i` term and
gives `ω∘R_i ≥ 0`.  A positive functional with `ω(R_i1) = 0` vanishes: `|ω(R_iw)| ≤ ‖w‖ω(R_i1)`.
So `ω = ω∘U_i`.  The dual complements check out both ways.  The A–S "compression" label is
still marked [unverified]; that is fine.

**§2 (B): STANDS.**  The `D_C` argument is correct: take `ℓ¹` within ε, and `L(a)` is bounded
for `a ∈ S`, so the estimate passes to the closure.  (i) ⟺ pointwise boundedness is correct
Banach–Steinhaus: `{L(a) : ‖a‖ ≤ 1}` are bounded operators on a Banach space.
"Chain combinations lie in `D_4`" is not checked here: it needs the layer bounds of
JordanFromChains (UNCLEAR, not load-bearing).  The spin-factor non-bound is correct and
elementary: `g(K)` is a vector space and the stabiliser `so(2)` is nonzero.

**§3 (H): STANDS.**  No Banach–Lie group structure on `G` is needed.  The inverse function
theorem is applied to the map `F = exp∘L̄(·)1 : W → W` (smooth, `dF(0) = id`), not to `G`.
Every `g ∈ G` is a linear homeomorphism preserving `int K`, so `G·1` is open.  Thompson:
`K` is closed and normal in the order-unit norm, and `int K` is a single part, so `d_T`
gives the norm topology there.  Order automorphisms are `d_T`-isometries, so the closedness
step is correct.  `e^{L(a)} ∈ Aut(K)` for `a ∈ W` follows from norm limits of
automorphisms and their inverses (the cone is closed).
Cor. (a) needs the two norms to be equivalent ("same Banach space" covers that).  JB
multiplications are order derivations of the JB cone, so `G·1 = int K_JB` too.

**§4 equivalence: STANDS.**  (J) and (P) are exactly `JBAlgebra.jordan` and `.sq_mem`.
`L(1) = T_i + T_{ci} = id`, and `L̄(a)1 = a` by continuity.  Commutativity and bilinearity
extend.  ⇒: in a JB-algebra `‖a∘b‖ ≤ ‖a‖‖b‖` in the order-unit norm (HOS 3.1.6), and the
product equals `L` on `S`.
**Commuting case: STANDS.**  `L̄(a∘b)c = L(c)L(a)b = L(a)L(c)b = L(a)L(b)c` on dense `S`,
so `∘` is associative.

**§4 numerics / "(K) is at least very close to (J)": BROKEN (overclaim).**  (K) does not
imply (J) for unital commutative algebras, and a counterexample exists already in dim 4,
the dimension searched.  Take `A = ℝ1 ⊕ span{x,y,z}` with `x² = y`, `xy = z`, `y² = z`,
and all other products of `x, y, z` zero.
* Every `[L_a,L_b]` is a derivation.  It kills `1, y, z` and maps into `ℝz`, and `z`
  annihilates `x, y, z`.  Checked by hand and exactly in numpy (residual 0).
* `A` is not Jordan: with `a = b = x`, `(x·x)·x² = y² = z` but `x·(x·x²) = xz = 0`.
  So `A` is not even power-associative.
General mechanism: the unital hull of any non-Jordan "Lie triple / almost Jordan" nil
algebra works, because `L_1 = id` drops out of every commutator.  Random restarts also
find such algebras for `m = 4, 5`.  The 60/60 result is a sampling artefact: generic
Levenberg–Marquardt limits are semisimple.
What survives: `A` is not formally real, so (K) + positivity ⇒ (J) is still open.
Literature pointer (from memory, [unverified]): Hentzel–Peresi, "Almost Jordan rings",
Proc. AMS 1988 — semiprime almost Jordan rings (char ≠ 2,3) are Jordan.  Osborn (1965) and
Petersson (Lie triple algebras) cover the identity.  If "Lie triple ⟺ almost Jordan"
holds, and (P) plus (i) give semiprimeness (formal reality: `a∘a = 0 ⇒ a = 0` looks
reachable from (P)), then **(K) ⇒ (J)** would follow with no trace form.  That is the
best lead here, but it still needs (K).  Rewrite the paragraph to say this.

**§4 "any proof of (J) must be non-tracial": UNCLEAR (heuristic).**  The absence of a
finite trace on `B(H)_sa` excludes one tool, not every invariant-form argument (for
example partial or weighted forms).  Downgrade "must" to "cannot use a global trace".
**Hua-type symmetry: minor gap.**  `s(e^{L(a)}1) := e^{−L(a)}1` needs every interior point
to be a single `e^{L(a)}1` and `a ↦ e^{L(a)}1` to be injective.  §3 only gives products of
exponentials.  This is labelled "candidate", so it is OK.

**§5: STANDS as heuristics.**  The two-projection `C(σ, M₂)` example is right.  "Three
projections generate all of `B(H)_sa`" needs complex generic projections, since real ones
generate only symmetric matrices; it is an existence claim, so fine.
**§6: UNCLEAR.**  The "ruled out" cases (`C(X)`, `ℓ^p` spin, deformations) are sketches.
Only the last one is argued (via §3(a)).  They are not load-bearing.

**Overclaims to fix:**
1. "(K) is at least very close to (J)" together with the 60/60 evidence (above).
2. §0 says "Remaining lemma … (J) and (P)", but it also needs (i) for the unbounded case.
   §4 states this correctly; §0's bullet is fine on a careful reading.
No error found in (N), (B), (H), or the Prop ⟺ (i)+(J)+(P) equivalence.
