# Can the rest of 9.43 be proved?  (`AlfsenShultzJordanTransplant` discharge plan)

Research note, 2026-09-26.  No Lean edits.  Inputs: JordanSymmetry.lean (the Prop :563,
`jordan_symmetry`, `IsOrderDerivation.lie`, `ExpIn.add`, `lemmaP`), Reconstruction.lean
(`IsOrderDerivation` :2276, `rec121` :2780, `spectral_rep` :1406, `spectral_dense(_core)`
:1785/:1975), Algebras.lean:263 (`JBAlgebra`), as948-*.md with Reviews, short.tex REC 121.
No copy of A–S; recollections marked [unverified].  **Everything below is claimed.**

Notation: `D_i := U_i − U_{ci}`, `T_i := ½(1 + D_i)`, `R_i := 1 − U_i − U_{ci}`; `i ⊥ j`
means `e_i + e_j ≤ 1`; `c` is an involution (injectivity), so `U_{ci}U_i = 0` too.
`JBAlgebra` asks: bilinear, commutative, unit 1, Jordan identity, `−1 ≤ a ≤ 1 ⇒
0 ≤ a² ≤ 1`, Banach OUS.  It does **not** ask `‖a*b‖ ≤ ‖a‖‖b‖`; any continuity
constant suffices, and continuity is only needed to extend from the span.

## 0. Verdict

* The Prop **as stated** (arbitrary dense span of the family) is **not provable by the
  9.43 route**: two ingredients A–S get from spectral duality are missing abstractly —
  (G1) a dense set of *chain* combinations `λ₀1 + Σ α_k e_{i_k}`, `e_{i_1} ≥ … ≥ e_{i_n}`,
  `α_k ≥ 0` (spectral resolutions inside the family), and (G2) compatibility:
  `U_i U_{cj} = U_{cj} U_i` for `e_j ≤ e_i`.  Truth of the Prop stays open.
* With (G1)+(G2) added as hypotheses, **every step is provable** from the rest (§1–§5),
  using only positivity, the closed form of `e^{tD_i}`, the kernel condition, and the
  (proved) symmetry.  REC's `V_A` supplies (G1) from `spectral_dense_core` (nested
  clopen level sets) and (G2) from SEA commutation.  **So REC 121 can be fully proved**
  and the named hypothesis dropped from rec102'/103'/136'.

## 1. Order lemmas for nested/orthogonal members (claimed; abstract)

Let `j ⊥ k` (both in the family).
* (O1) `U_j U_k = U_k U_j = 0`.  For `w ≥ 0`: `0 ≤ U_k w ≤ ‖w‖e_k ≤ ‖w‖e_{cj}`, and
  `U_j e_{cj} = U_jU_{cj}1 = 0`, so `0 ≤ U_jU_k w ≤ 0`.  Positives span.
* (O2) `U_{ck} U_j = U_j`.  `v := U_j w ≥ 0`, `U_k v = 0` by (O1), kernel condition.
* (O3) `U_j R_k = 0 = R_k U_j`, hence `U_j U_{ck} = U_j`.  `D_k` has `D_k^n = U_k +
  (−1)^n U_{ck}` (n ≥ 1), so `e^{tD_k} = e^t U_k + e^{−t} U_{ck} + R_k` (limit of
  `expPartialSum`, exact), positive.  `U_j e^{tD_k} w = e^{−t}U_jU_{ck}w + U_jR_k w ≥ 0`;
  `t → ∞`, closed cone: `U_jR_k ≥ 0`.  `U_jR_k 1 = U_j(1 − e_k − e_{ck}) = 0`; a positive
  map killing 1 is 0.  `R_kU_j = U_j − U_kU_j − U_{ck}U_j = 0` by (O1),(O2).
* Nested form (`e_j ≤ e_i` ⇔ `j ⊥ ci`): `U_iU_j = U_jU_i = U_j`, `U_{cj}U_{ci} =
  U_{ci}U_{cj} = U_{ci}`, `U_jU_{ci} = U_{ci}U_j = 0`.  Hence
  `4[T_i, T_j] = [D_i, D_j] = −[U_i, U_{cj}]` — the only commutator not killed is (G2).
* Consequences used below: `T_i e_j = e_j` for `e_j ≤ e_i` (`U_ie_j = U_iU_j1 = e_j`,
  `U_{ci}e_j = 0`); `T_j e_k = 0` for `j ⊥ k`; `‖U_i‖ ≤ 1`, `‖D_i‖ ≤ 1`, `‖T_i‖ ≤ 1`
  (`w ∈ [−1,1] ⇒ U_iw ∈ [−e_i,e_i]`, `U_{ci}w ∈ [−e_{ci}, e_{ci}]`); `e_i = 1 ⇒ U_i = id`
  (`e^{tD_i}`, t → −∞: `1 − U_i ≥ 0` kills 1) and `e_i = 0 ⇒ U_i = 0`.

**(G2) abstractly.**  With `p := e_j ⊥ q := e_{ci}` (so `U_{p'} = U_{cj}`, `U_{q'} = U_i`) one gets
`[D_p, D_q] = [U_{p'}, U_{q'}] = [R_p, R_q]`, an order derivation (`lie`) killing 1
(symmetry) and killing/killed by `U_p, U_q`.  I could not show it vanishes; the
two-parameter family `e^{sD_p}e^{tD_q}` gives only `U_p + U_q + R_pR_q ≥ 0`-type limits.
In A–S, compatible compressions commute via the P-projection pairing with `V`
[unverified].  **Open abstractly.**

## 2. Step 1 — well-definedness (claimed; abstract, no G1/G2)

For a representation `a = Σλ_k e_{i_k}` put `T_a := Σλ_k T_{i_k}` (bounded, a finite
combination).  If `Σλ_k e_{i_k} = 0` then `Σλ_k T_{i_k} b = Σλ_kμ_l T_{j_l} e_{i_k} =
Σμ_l T_{j_l}(Σλ_k e_{i_k}) = 0` for `b = Σμ_l e_{j_l}` (symmetry), so the bounded operator
vanishes on the dense span, hence is 0.  So `a ↦ T_a` is a **linear map span → B(W)**, with
`T_a b = T_b a` on span, `T_a 1 = a`, `T_1 = T_i + T_{ci} = id` (`1 = e_i + e_{ci}`).
Answer to the brief: yes, symmetry suffices despite linear dependencies — the dependency
is killed by pairing with the other factor, then by density.  Lean: ~120 lines
(`Finsupp`/`List` sums; `Submodule.span`; bounded-op vanishing on dense set).

## 3. Step 2 — continuity and extension (claimed; needs G1)

Chain element: `a = λ₀1 + Σ_{k=1}^n α_k q_k`, `q_k := e_{i_k}` nested decreasing, `α_k ≥ 0`.
Layers `p_j := q_j − q_{j+1}` (`q_0 := 1`, `q_{n+1} := 0`), `λ_j := λ₀ + Σ_{k≤j} α_k`
(monotone).  Positive maps `Φ_j := U_{c q_{j+1}} U_{q_j}` satisfy `Φ_j 1 = p_j` and
`Φ_j a = λ_j p_j` (§1: `U_{q_j}q_k = q_j` for `k ≤ j`, `= q_k` for `k > j`;
`U_{cq_{j+1}}q_j = p_j` by the kernel condition since `U_{q_{j+1}}p_j = 0`;
`U_{cq_{j+1}}q_k = 0` for `k > j`).  Hence `|λ_j| ≤ ‖a‖` whenever `p_j ≠ 0`.
Then `‖T_a‖ ≤ |λ_bot| + (λ_top − λ_bot) ≤ 3‖a‖`, where bot/top are the extreme
non-degenerate layers (degenerate layers: `q_j = q_{j+1}` ⇒ same index ⇒ contributes 0;
`q_1 = 1` or `q_n = 0` ⇒ `T = id`/`0`, merge into `λ₀`).
Extension: for `a` in span and `b` a chain element, `‖T_a b‖ = ‖T_b a‖ ≤ 3‖b‖‖a‖`;
`T_a` bounded and chains dense (G1) ⇒ `‖T_a w‖ ≤ 3‖a‖‖w‖` ∀w.  So `a ↦ T_a` is a
bounded linear map span → `W →L W`; extend to `W` (`ContinuousLinearMap.extend` along
the dense submodule; the normed structure from `ousNorm` is already in JordanSymmetry).
`a * w := T̄_a w` is jointly continuous bilinear, `e_i * w = T_i w` by construction.
Lean: ~300 lines (degenerate-layer bookkeeping is the tedious part).
*Without G1* the brief's question has no answer: bounding `‖T_a‖` by `‖a‖` for an
arbitrary representation needs a spectral one; `T_a` is an order derivation with
`T_a1 = a` (`ExpIn.add`), but order derivations with given `δ1` are unbounded in norm
(add Jordan derivations), so that route fails.

## 4. Step 3 — commutativity, unit, bilinearity (claimed; trivial)

`T_a b = T_b a` on span × span, continuity ⇒ `mul_comm`.  `mul_one`: `T_a 1 = a` on span,
extend.  `one_mul`: `T_1 = id`.  `add_mul`, `smul_mul`: linearity of the extension.
Lean: ~80 lines.

## 5. Step 4 — Jordan identity (claimed; needs G1 + G2)

For a chain element `a`: `a*a = Σ_{k,l} …` computed with `T_{q_k} q_l = q_{max(k,l)}`
(nested, §1) and `T_{q_k}1 = q_k`, stays in `span{1, q_1..q_n}` (it is `Σ_j λ_j² p_j`).
All `T_{q_k}` commute pairwise (§1 nested lemma + G2), so `T_a` and `T_{a*a}` commute:
`(a*b)*(a*a) = T_{a²}T_a b = T_aT_{a²}b = a*(b*(a*a))` ∀b.  Both sides are continuous
in `a` (trilinear, jointly continuous), chains dense ⇒ identity for all `a`.
This matches A–S's proof (T_p, T_q commute for compatible p, q; a and a² share a
spectral resolution) [unverified].  Lean: ~200 lines.
*Abstractly without G2*: fails at exactly `[U_i, U_{cj}] = 0`; no counterexample known.

## 6. Step 5 — `−1 ≤ a ≤ 1 ⇒ 0 ≤ a² ≤ 1` (claimed; needs G1 only)

Chain `a`: `a*a = Σ_j λ_j² p_j` (§5, a formal identity in `q`'s).  `−1 ≤ a ≤ 1` and
`Φ_j a = λ_jp_j`, `Φ_j1 = p_j` give `|λ_j| ≤ 1` on non-degenerate layers; `p_j ≥ 0`,
`Σ_j p_j = 1` ⇒ `0 ≤ a*a ≤ 1`.  General `a`: chains `a_n → a`, rescale by
`max(1, ‖a_n‖)` (stays a chain, stays in `[−1,1]` by Archimedean), continuity of
squaring + closed cone.  Lean: ~200 lines.

## 7. REC's `V_A` supplies G1 and G2 (claimed; check the code)

* **G1.**  `spectral_dense_core` approximates `2NΨ(b,f) − N·1` by combinations of the
  idempotents from the clopen level sets `closure{f > j/n}`, `j = 0..n−1`: nested
  decreasing, equal positive steps `2N/n` — a chain in the required form.  Needs a
  re-export stating nesting (`≤` in `Pred`, from `spec_G_bot_mono`) and `α ≥ 0`.
  **Check** how the Boolean part `b` enters (the idempotents may be `Ψ(b ⊓ ·, χ_j)` or
  similar; nesting should survive).  ~100–200 lines.
* **G2.**  `e_j ≤ e_i` sharp ⇒ `q_j` commutes with `q_i` and `q_i^⊥` (SEA: comparable
  sharp elements commute; alternatively all chain members lie in `{a}''` so commute
  outright).  Then `Uop` of commuting predicates commute: `Commutes.assoc` plus
  `a⊙b = b⊙a` gives `p⊙(q⊙x) = (p⊙q)⊙x = (q⊙p)⊙x = q⊙(p⊙x)`, extended linearly by
  `gp_linearMap_ext`.  ~60 lines.  It suffices to have G2 for chain members only.
* Only these two facts are REC-specific; no states, no REC 119 beyond `rec120`.

## 8. Plan and cost

1. Abstract theorem `jordanTransplant_of_chains`: the Prop's hypotheses, with density
   replaced by G1 (chain density) and G2 added (for chain members), conclusion as the
   Prop.  Pieces: §1 order lemmas ~150; §2 ~120; §3 ~300; §4 ~80; §5 ~200; §6 ~200.
   Subtotal ≈ 1050 lines (±40%).
2. REC side: chain-form `spectral_dense` + G2 + `rec121''` rewired, `rec102''/103''/136''`
   without `AlfsenShultzJordanTransplant` ≈ 250–400 lines.
3. Keep `AlfsenShultzJordanTransplant` as a stated, unused, open Prop (or delete); record
   that the 9.43 transplant needed spectral chains + compatibility, which REC has.

**Recommendation: attempt the full discharge**, via (1)+(2), after an adversarial review
of §1 (O3 and the `e^{tD}` closed form), §3 (the layer maps Φ_j and the extension
argument) and §7 (that `spectral_dense_core`'s idempotents really are nested and
commuting).  Build order: §1 → §2 → §7 G1 re-export (cheap early check that the REC side
fits) → §3 → §4/§5/§6.  If §3's degenerate-layer bookkeeping balloons, fall back to
requiring non-degenerate chains in G1 (REC can drop empty level sets).  Do not try to
prove the Prop as stated: G1 is spectral theory for an arbitrary family and G2 is open.

## Claimed, for adversarial review
1. (O1)–(O3), nested corollaries, `4[T_i,T_j] = −[U_i,U_{cj}]` for `e_j ≤ e_i`.
2. Well-definedness of `a ↦ T_a` on span from symmetry + density alone.
3. Layer maps `Φ_j a = λ_jp_j`; `‖T_a‖ ≤ 3‖a‖` on chains; extension via `T_a b = T_b a`.
4. Jordan identity on chains from commuting `T_{q_k}`; density transfer.
5. `a*a = Σλ_j²p_j` on chains; `sq_mem`.
6. REC: `spectral_dense_core` yields nested chains with `α ≥ 0`; G2 from SEA commutation.
7. G1, G2 are not derivable abstractly by these methods (not claimed false).

## Review (2026-09-26)

Adversarial review; no Lean.  Sources re-read: JordanSymmetry.lean:563 (the Prop),
Algebras.lean:263 (`JBAlgebra`), Reconstruction.lean:1406 (`spectral_rep`), :1785
(`spectral_dense_core`), :1975, :2276 (`IsOrderDerivation`), :2448 (`Uop`), :2781
(`rec121`), SEA/Basic.lean:661/733 (`Commutes`, `Commutes.assoc`).  Numerical sanity
check in `Sym_4(ℝ)` with `U_p x = pxp` (scratch rev943-check.py): the `e^{tD}` closed
form, `T_a b = a∘b` for a chain, `Φ_j a = λ_j p_j`, `Φ_j 1 = p_j`, and
`[D_i,D_j] = −[U_i,U_{cj}]` all hold to 1e-15.

**Claim 1 (O1–O3, nested corollaries, commutator): STANDS.**  `c` is not assumed an
involution, but `e(c(c i)) = e i` + injectivity gives it, so `U_{ci}U_i = 0` is
available.  `D_k^2 = U_k + U_{ck}` uses only idempotence of `U_k, U_{ck}` and the two
cross products vanishing; no commutation or idempotence of `R_k` is needed, so
`e^{tD_k} = e^tU_k + e^{−t}U_{ck} + R_k` is exact (partial sums, uniqueness of limits).
`IsOrderDerivation` gives an order iso equal to that limit, hence positive.  O3's
`t → ∞` uses the closed cone (Archimedean); "positive + kills 1 ⇒ 0" uses `R_k1 = 0`
(trivially, `e_k + e_{ck} = 1`) and antisymmetry.  Nested translation `e_j ≤ e_i ⇔
j ⊥ ci` and all six products check; `[U_i,U_j] = [U_{ci},U_j] = [U_{ci},U_{cj}] = 0`.

**Claim 2 (well-definedness): STANDS.**  Symmetry hypothesis is literally
`2T_i e_j = 2T_j e_i`; the pairing argument plus boundedness of positive maps and
the density hypothesis suffices.  `1 ∈ span` via `e_i + e_{ci}`.  (Empty `ι` forces
`W = 0`; harmless.)

**Claim 3 (layers, `‖T_a‖ ≤ 3‖a‖`, extension): STANDS.**  Φ_j computation correct
with the conventions `U_{q_0} := id`, `U_{c q_{n+1}} := id` (q_0 = 1, q_{n+1} = 0 need
not be family members — state Φ_0, Φ_n separately in Lean).  The bound needs only the
two extreme layers non-degenerate; the normalisation (drop `q_k = 1` via `U = id`,
`q_k = 0` via `T = 0`, merge equal `q`'s by injectivity) is sound.  Extension: for
`a ∈ span`, `b` a chain, `‖T_a b‖ = ‖T_b a‖ ≤ 3‖b‖‖a‖`; `T_a` continuous and chains
dense ⇒ `‖T_a‖ ≤ 3‖a‖`.  Bound on one factor only on chains is enough — valid.

**Claim 4 (Jordan): STANDS.**  `T_{q_k}q_l = q_{max}` (nested + symmetry), `a*a` stays
in `span{1,q_k}`, `T_{a²}` is a combination of commuting `T_{q_k}` (nested lemma + G2
for pairs *within one chain*).  Rewriting both sides as `T_{a²}T_a b`, `T_aT_{a²}b`
uses `mul_comm` (proved first).  Density transfer: for fixed `b` both sides are
compositions of a jointly continuous bilinear map — continuous in `a`; equality set
closed.  Fine (degree is irrelevant).

**Claim 5 (`sq_mem`): STANDS.**  `T_{p_j}p_l = δ_{jl}p_j` checked from `T_{q_k}q_l =
q_{max}` incl. the `q_0 = 1`, `q_{n+1} = 0` ends.  Rescaling by `max(1,‖a_n‖)` keeps
`α ≥ 0` and lands in `[−1,1]` (‖x‖ ≤ 1 ⇒ −1 ≤ x ≤ 1).

**Claim 6 (REC supplies G1, G2): G1 BROKEN as written, repairable; G2 STANDS.**
`spectral_dense_core`'s list is `[(2N, Ψ(b,0)), (−N, 1)] ++ [(2N/n, Ψ(⊥,χ_j))]_{j<n}`.
`Ψ(b,0)` and `Ψ(⊥,χ_j)` are *orthogonal* (disjoint Boolean/continuous parts), not
nested, so this list is **not a chain** and no "re-export stating nesting" exists.
Repair: since `n · 2N/n = 2N` and `gmap Ψ(b,χ_j) = gmap Ψ(b,0) + gmap Ψ(⊥,χ_j)`
(`spec_G_add`), the same vector is `−N·1 + Σ_j (2N/n)·Ψ(b,χ_j)`, and
`Ψ(b,χ_{j+1}) ≤ Ψ(b,χ_j)` (closure monotone ⇒ `χ_{j+1} ≤ χ_j`, then `spec_G_add`
with `b' = ⊥`), `Ψ(b,χ_j)` idempotent (`spec_idem`).  So G1 holds with a *new list*,
a proof change in `spectral_dense_core` (~100–150 lines), not a re-export.
G2: chain members `Ψ(b,χ_j)` lie in the range of the multiplicative `Ψ`, so they
`⊙`-commute; commuting with `q` ⇒ commuting with `q^⊥` (SEA axiom; or write
`orth Ψ(b,χ) = Ψ(bᶜ, 1−χ)`).  `Commutes.assoc` both ways gives
`p⊙(q⊙x) = q⊙(p⊙x)` on generators, `gp_linearMap_ext` extends.  Valid as maps on V_A.
Advice: bundle G2 into the chain hypothesis ("members of each approximating chain
pairwise satisfy G2") so REC needs only the Ψ-range argument, not a general
"comparable sharp elements commute" SEA lemma.

**Claim 7 (G1, G2 not abstract): UNCLEAR** (not claimed false; not attacked further).

**JBAlgebra fields:** IsOUS, banach, mul_comm, mul_one, one_mul, jordan, sq_mem,
add_mul, smul_mul — all delivered by §3–§6; no norm/submultiplicativity or
continuity field.  Confirmed.  `IsDirectedCompleteOUS` is unused.

**Cost:** 1050 ±40% abstract is optimistic for Lean (656 lines bought only the
symmetry); `ContinuousLinearMap.extend` from a non-closed submodule with `ousNorm`
coercions, list/Finsupp chain bookkeeping and the layer normalisation each tend to
double.  Expect 1500–2200 total incl. REC (~350–500 with the G1 list rewrite).

**Recommendation: GO WITH CHANGES** — (i) G1 on the REC side via the rewritten list
`Ψ(b,χ_j)`, not a nesting re-export; build it first as the cheap feasibility check;
(ii) state G2 per chain in the abstract hypothesis; (iii) formulate chains with
explicit non-degeneracy (q_1 ≠ 1, q_n ≠ 0, strictly decreasing) to skip the
normalisation (REC drops empty/full level sets, or merges them into λ₀);
(iv) budget ~1.5× the note's estimate.
