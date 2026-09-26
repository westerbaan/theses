# REC 136 without exchangeable families: a Barnum–Graydon–Wilce-style no-go, REC-native

Research note, 2026-09-26. All results **claimed** (not reviewed, nothing compiled).
Numerical checks: scratch `r136n-alb.py` (Albert algebra as 27-dim numpy model).

## 0. Result in one paragraph

REC 135 ("every `V_A` is JW", scalars `[0,1]`) follows from **REC 52** (as
`JBWExceptionalSummand`) plus only **part (ii)** of `ExceptionalAlbertPoint` (a
multiplicative `χ : V → Alb` with `χ 1 ≠ 0` for every non-zero purely exceptional JBW `V`),
plus a **finite-dimensional lemma about `Alb` alone** (§3), using the object
`X = (W ⊗ W) ⊗ W` and REC 126/127 only. Part (i) (exchangeable families, REC 133/134,
REC 128) is not used; no tower, no bounded-rank ideal, no symmetries. The finite-dim lemma
needs no Jordan structure theory: the single-idempotent Peirce identity (`idem_peirce`), the
EJA spectral theorem (`spectral_family`, idempotents in `Calg a`), the Albert cubic
(`cubic`), and an explicit embedding `ℝp₁ ⊕ ℝp₂ ⊕ ℝp₃ ↪ ℂ³`. No spin factors, no Clifford
algebras, no coordinatization, no classification.

Answer to the three aims: (a) yes — the hypothesis is (ii) alone, which is incomparable
with `ExceptionalBoundedRank` (drops (i) entirely, keeps the Albert target); (b) no —
some finite-dim input about `Alb` is unavoidable (§5); (c) the obstruction to (b) is that
"purely exceptional" gives no handle without a concrete target; (ii) is the cheapest one
and follows from the JB-level Alfsen–Shultz–Størmer Gelfand–Naimark theorem (H-O–S §7.2),
not only from Shultz 1979 (number unverified offline).

## 1. What BGW use, and what REC supplies

Barnum–Graydon–Wilce (Quantum 4:359, 2020) define a composite `AB` of EJAs by a bilinear
unital positive `⊗ : A × B → AB` such that `a ⊗ 1` and `1 ⊗ b` operator commute and
`a ↦ a ⊗ 1` is a unital Jordan hom; their no-go for the Albert algebra runs on those
data plus the EJA classification (a simple summand of `AB` containing `Alb` unitally is
`Alb`, forcing `B`'s image central). REC supplies exactly these data: `tensV` (bilinear,
positive, `1 ⊗ 1 = 1`), REC 126 (`rec126`, proved in full: `T_{a⊗1} T_{1⊗b} = T_{1⊗b}
T_{a⊗1}` on all of `V_{A⊗B}`), REC 127 (`rec127`, `rec127_right`: `a ↦ a ⊗ 1`,
`b ↦ 1 ⊗ b` Jordan homs), `tens_ne_zero`. REC 128 (two-block only) is **not** needed.
The classification is replaced by §3, which is why three tensor factors appear.

## 2. The REC-side argument (all pieces exist in `Rec136Hyps.lean` / `Monoidal.lean`)

Let `A` be an object, `σs = realSplit ψ₀`. As in `rec135_weak`: REC 52 gives `V_A` JW or a
central idempotent `c ≠ 0`; `corner_of_summand` gives `W` with `V_W` purely exceptional,
`1_W ≠ 0`. Put `X := (W ⊗ W) ⊗ W` and the three unital Jordan homs
`ι₁ a = (a⊗1)⊗1`, `ι₂ b = (1⊗b)⊗1`, `ι₃ c = 1⊗c` (`rec127`, `rec127_right`, composed).
Operator commutation (REC 126): `ι₁, ι₂` commute **on the subalgebra `R₁₂ := (V_{W⊗W})⊗1`**
(image of `rec126` in `V_{W⊗W}` under the Jordan hom `u ↦ u⊗1`), and `ι₁, ι₂` each commute
with `ι₃` on all of `V_X` (`rec126` in `V_X`). No associator is needed: §3 only ever uses
`T_p T_y p = T_y T_p p` for `p, y` in a common subalgebra on which commutation holds.

Apply `JBWExceptionalSummand` to `V_X` exactly as in `tower_absurd`: JW is absurd (`ι₁`
would be a non-zero Jordan hom of `V_W` into a C*-algebra); otherwise `corner_of_summand`
gives `W'`, `π : V_X → V_{W'}` unital surjective Jordan, and (ii) gives `χ`; set
`ψ := χ ∘ π : V_X → Alb`, multiplicative, `e := ψ 1` a non-zero idempotent. Put
`S_i := ψ(ι_i V_W) ⊆ Alb₁(e)` (unital subalgebras, unit `e`), `R := ψ(R₁₂) ⊇ S₁ ∪ S₂`,
`R' := ψ(V_X) ⊇ all`. Commutation transports along `ψ` (multiplicative) to `R`, `R'`.
The purely exceptional hypothesis is used only as: **any Jordan hom `V_W → 𝔅` (C*) is 0**,
so each `S_i` is *not* contained in the span of an orthogonal family of idempotents of
`Alb` (else `ψ ∘ ι_i` followed by coordinates would be a non-zero Jordan hom into `ℂⁿ`,
`ψ ι_i 1 = e ≠ 0`). §3 contradicts this.

## 3. The finite-dimensional lemma (claimed; every step checked numerically)

**Lemma (three-way no-go in `Alb`).** Let `e ∈ Alb` be a non-zero idempotent,
`S₁, S₂, S₃ ⊆ Alb₁(e)` unital Jordan subalgebras, `R ⊇ S₁ ∪ S₂`, `R' ⊇ S₁ ∪ S₂ ∪ S₃`
subalgebras with `T_x T_y = T_y T_x` on `R` for `x ∈ S₁, y ∈ S₂`, and on `R'` for
`x ∈ S₁ ∪ S₂, y ∈ S₃`. Then some `S_i` lies in the span of ≤ 3 orthogonal idempotents.

Ingredients (E1–E5), all elementary in `Alb`:
* E1 (Peirce, `idem_peirce`): `y` op-commutes with idempotent `p` (on a subalgebra
  containing both) ⇒ `p(py) = py` ⇒ `y ∈ Alb₀(p) ⊕ Alb₁(p)` (`y_½ = 4(L−L²)y = 0`).
* E2 (trace/rank, from `cubic`): idempotent `p` satisfies `(T−S−1)p + N·1 = 0` with
  `S = (T²−T)/2`, so `T p ∈ {0,1,2,3}`; `T` additive, `T 1 = 3`, `T p = ⟨p,p⟩`
  (`idem_inner_one`), so `T p = 0 ⇔ p = 0`, and `T e = 3 ⇒ e = 1`.
* E3 (`spectral_family` + `Calg a ⊆ S` for a finite-dim unital subalgebra `S ∋ a`): a
  unital subalgebra of `Alb` with only trivial idempotents is `ℝ·unit`.
* E4 (E2+E3): `T p = 1 ⇒ Alb₁(p) = ℝp` (an idempotent `q ≤ p` has `T q ∈ {0,1}`, so
  `q ∈ {0,p}`).
* E5: for `p ≤ e` idempotents, `Alb₁(e) ∩ Alb₀(p) = Alb₁(e−p)` and `Alb₁(e−p) ⊆ Alb₀(p)`;
  `C := Alb₁(f)` is a subalgebra; `p ⊥ f ⇒ p ∘ C = 0` (easy from E1's calculus).

Proof. By E3, `S₁ ≠ ℝe` has an idempotent `p₁ ∉ {0,e}`; `p₂ := e − p₁ ∈ S₁`. By E2,
`(T p₁, T p₂) ∈ {(1,1), (1,2), (2,1)}` (if `T e = 1`, `S₁ ⊆ Alb₁(e) = ℝe` by E4).
*Case (1,1)*, `T e = 2`: for `y ∈ S₂`, E1 with `p₁` (on `R`) and E4, E5 give
`y ∈ ℝp₁ ⊕ (Alb₁(e) ∩ Alb₀(p₁)) = ℝp₁ ⊕ Alb₁(p₂) = ℝp₁ ⊕ ℝp₂`. Done.
*Case (1,2)* (swap `p₁, p₂` for (2,1)), `e = 1`: E1, E4, E5 give
`S₂, S₃ ⊆ ℝp₁ ⊕ C`, `C := Alb₁(p₂)` (rank 2). `ρ : ℝp₁ ⊕ C → C` is a Jordan hom (E5,
`p₁ ∘ C = 0`). If `ρ(S₂) = ℝp₂` then `S₂ ⊆ ℝp₁ ⊕ ℝp₂`, done; else (E3) `ρ(S₂)` has
`q₁ + q₂ = p₂`, both non-zero, `T q_j = 1` (E2). Pick `q ∈ S₂` with `ρ q = q₁`,
`q = γp₁ + q₁`. For `y = δp₁ + y' ∈ S₃` (`y' ∈ C`), commutation on `R'` gives
`q(qy) = qy`; expanding with `p₁ ∘ C = 0` yields `q₁(q₁y') = q₁y'`, so by E1, E4, E5
`y' ∈ ℝq₁ ⊕ (C ∩ Alb₀(q₁)) = ℝq₁ ⊕ Alb₁(q₂) = ℝq₁ ⊕ ℝq₂`; hence
`S₃ ⊆ ℝp₁ ⊕ ℝq₁ ⊕ ℝq₂`. Done. ∎

Numerics (`r136n-alb.py`): `[T_{E₁₁}, T_{E₁₂}] ≠ 0`; op-commutant of `Alb` is `ℝ1`;
random idempotents (via `exp[T_a,T_b]`) have `T ∈ {1,2,3}`, `dim Alb₁ = 1, 10, 27`;
E1 holds (`y ∈ Alb₀⊕Alb₁` op-commutes, `y ∈ Alb_½` does not); for a rank-1 frame,
`{y : y_½(p_i) = 0 ∀i}` is 3-dimensional.

Why three factors: with two (`X = W ⊗ W`) case (1,2) ends with a non-special
`ρ(S₂)` inside the rank-2 corner `C ≅` spin factor `J(ℝ⁹)`, and the contradiction needs
"rank-2 corners of `Alb` are JC" (Clifford embedding). The third commuting factor
replaces the Clifford algebra by one more application of E1.

## 4. Cheap improvement to the existing route (independent of §2–3)

`tower_absurd` counts against `dim Alb = 27`; E2 gives rank 3, so with (i) a 2-family
`q₁, q₂` in `V_W` already gives 4 mutually exchangeable non-zero orthogonal idempotents
`q_i ⊗ q_j` in `V_{W⊗W}` (REC 134) with all-or-none images — `4 > 3`, no tower induction,
one tensor step (`n² ≥ 4 > 3` for every `n ≥ 2`). `alb_orth_idem_card_le` → trace bound.

## 5. What cannot be removed, and comparison

* Some concrete finite-dimensional target is needed: "purely exceptional" is a negative
  property (no Jordan hom into C*-algebras) and yields nothing positive by itself; every
  REC-native argument must land in an algebra where rank counting is possible. (ii) is the
  weakest such input on offer; it is a corollary of Shultz Thm 3.9 *or* of the JB-level
  A–S–S Gelfand–Naimark theorem (`V ↪ B(H)_sa ⊕ C(X, Alb)`, purely exceptional ⇒ first
  component 0 ⇒ `X ≠ ∅`, evaluate at a point). Neither the abstract bounded-rank form nor a
  "finite quotient" suffices for §3, which uses the Albert cubic (E2) and Peirce in `Alb`.
* REC 52 is still used twice (on `V_A`, on `V_X`), as in `rec135_weak`; the abstract-JBW
  no-go "`V_X` contains three pairwise op-commuting purely exceptional unital subalgebras"
  has no proof without a structure theorem.
* Angles (2)/(3) (single idempotent + swap): the swap `Pred(β)` is a Jordan automorphism
  exchanging `p⊗(1−p)` and `(1−p)⊗p`, but not by a symmetry, and an automorphism-exchange
  gives no all-or-none property at a point evaluation (automorphisms of `C(Y, Alb)` move
  points). Rank counting of `p⊗p, p⊗p⊥, p⊥⊗p, p⊥⊗p⊥` gives nothing without all-or-none
  (two non-zero cells cover all marginals, for any number of factors). Dead end; §3 is
  what replaces it.
* Hypothesis comparison: new route = `JBWExceptionalSummand` + (ii) + Lemma §3 (provable,
  est. 600–1000 lines: E1–E5 ≈ 300, case analysis ≈ 300, `ℂ³` C*-algebra glue ≈ 100) +
  ≈ 150 lines of REC glue (three homs, commutation transport). Current route =
  `JBWExceptionalSummand` + (i) + bounded rank. Strictly fewer *literature* hypotheses
  (no (i), i.e. nothing about symmetries in purely exceptional algebras).

## 6. Suggested Lean statement (not written)

```
def ExceptionalAlbertMap : Prop := ∀ V ..., JBWAlgebra V → IsPurelyExceptional V →
  ouUnit V ≠ 0 → ∃ χ : V →ₗ[ℝ] Alb, (∀ a b, χ (a*b) = χ a * χ b) ∧ χ (ouUnit V) ≠ 0
theorem alb_threeway_nogo (e : Alb) (he : e*e = e) (he0 : e ≠ 0) (S₁ S₂ S₃ R R' : Submodule ℝ Alb)
  ... : ∃ i, ∃ (n : ℕ) (_ : n ≤ 3) (p : Fin n → Alb), orth-idem p ∧ S_i ≤ span (range p)
theorem rec135_albmap (hP : JBWExceptionalSummand) (hS : ExceptionalAlbertMap) (A : C) : IsJW (V_A)
```

## Review (2026-09-26)

Adversarial review (no Lean, no compile). Scratch: `rev136n-c.py`, reusing `r136n-alb.py`.
**Overall: STANDS, with two small gaps in §3 that are easy to fix (G1, G2).** No counterexample
to the lemma exists: the proof below is complete once G1/G2 are patched.

**REC side (§2): STANDS.**
- `rec126` (Monoidal.lean:1669) is exactly `J(a⊗1)(J(1⊗b) v) = J(1⊗b)(J(a⊗1) v)` for all
  `v ∈ V_{A⊗B}`, i.e. full operator commutation in `V_{A⊗B}`. With `A := W⊗W, B := W` it gives
  `ι₁, ι₂` vs `ι₃` on all of `V_X` (both `ι₁ a, ι₂ b` have the form `u ⊗ 1`). For `ι₁` vs `ι₂`, push
  `rec126` in `V_{W⊗W}` through the Jordan hom `u ↦ u⊗1` (`rec127` part 1). That gives commutation
  only on the image `R₁₂`, as the note says. No associator is used.
- Transport along a multiplicative `ψ`: `ψ(x(yz)) = ψx(ψy ψz)`, so commutation holds on `ψ(R₁₂)`
  and on `ψ(V_X)`. Unit: `ψ(ι_i 1) = ψ 1_X = e ≠ 0` (π unital, `χ 1 ≠ 0`), so `S_i ⊆ Alb₁(e)`. OK.
- The lemma uses commutation only in the form `T_p T_y p = T_y T_p p` with `p, y ∈ R` (resp. `R'`).
  Checked: E1 is `p(yp) = y(pp) = yp`, and case (1,2) is `q(yq) = y(qq)`. Both only need `p, q ∈ R`.
- Pure exceptionality (`Algebras.lean:332`: every Jordan hom into a C*-algebra of universe `v` is 0).
  If `S_i ⊆ span{p₁..p_n}` with the `p_k` orthogonal, the coordinate map composed with `ψ ∘ ι_i` is a
  Jordan hom with value `≠ 0` at 1. Universe glue: land in `C(ULift.{v} (Fin n), ℂ)` (Mathlib has
  `CStarAlgebra C(α, A)`), not in `ℂⁿ : Type`. OK.

**Finite-dimensional lemma (§3): STANDS after fixes.**
- E1: OK (`y_½ ≠ 0 ⇒ L_p² y − L_p y ≠ 0`, since the eigenvalue ½ gives −¼).
- E2 via `cubic` (Albert.lean:347): `S x = (T x² − ⟨x,x⟩)/2`. For `p² = p` with `⟨p,p⟩ = T p`, this
  gives `(1 − T + S)p = N·1`. So either `p ∈ ℝ1` or `T² − 3T + 2 = 0`. Hence `T p ∈ {0,1,2,3}`. OK.
- E4, E5: standard; confirmed numerically (`dim C = 10`, `p₁∘C = 0`, and `{y' ∈ C : y'_½(q₁) = 0}`
  has dim 2 = `ℝq₁ ⊕ ℝq₂`).
- Case analysis: all cases are covered (`Te = 1`; `Te = 2` forces (1,1); `Te = 3` gives (1,2)/(2,1)).
  Which pairs are used: S₁–S₂ on `R`, S₁–S₃ and S₂–S₃ on `R'`. All three are supplied.
- **G1 (gap, fixable).** Case (1,2) picks `q ∈ S₂` with `ρ q = q₁` and uses `q(qy) = qy`. That needs
  `q² = q`, which fails for `q = γp₁ + q₁` with `γ ∉ {0,1}`. Fix: in that case
  `p₁ = (q − q²)/(γ − γ²) ∈ S₂`, so `q₁ ∈ S₂`, and then take `q := q₁`. Otherwise `q` is already an
  idempotent. The rest goes through: `p₁∘C = 0` gives `q₁(q₁y') = q₁y'`.
- **G2 (Lean gap, fixable).** `Calg a = closure(span{jpow a n})` contains `jpow a 0 = 1`, so
  "`Calg a ⊆ S`" is false for `S` with unit `e ≠ 1`. Fix: apply E3 to the unital subalgebra
  `S ⊕ ℝ(1−e)` of `Alb` (`(1−e)∘Alb₁(e) = 0`), then intersect with `Alb₁(e)`. This is about +40 lines.
- Counterexample search: none is possible given the proof. The only freedom is a non-associative
  `ρ(S₂)` inside the spin corner `C`. The S₂–S₃ commutation, plus the rank-1-ness of `q₁`, kills it.

**§4 (cheap improvement): STANDS.** A Jordan hom preserves `U` (`U_a b = 2a(ab) − a²b`), so
`ψ(q_i⊗q_j) = 0 ⇔ ψ(q_k⊗q_l) = 0`. Four non-zero orthogonal idempotents summing to `e` give
`T e ≥ 4 > 3`. Caveat: this needs the Albert target, i.e. `ExceptionalAlbertPoint` (both parts). It
does **not** apply to the abstract-`D` `ExceptionalBoundedRank`.

**§5 claims.** Incomparability with `ExceptionalBoundedRank`: OK as Props. (ii) gives a ≤27-dim
quotient but not (i). The H-O–S number for A–S–S Gelfand–Naimark was left unverified (the note flags
this); the argument from it is correct. "Three factors avoid Clifford" was not independently checked.
It is only motivation.

**Props REC 136 would need:** `JBWExceptionalSummand` (from REC 52, as now) +
`ExceptionalAlbertMap` (= part (ii) of `ExceptionalAlbertPoint` alone). Nothing else. The lemma is
provable from `Albert.lean` + `Appendix2.lean`. Estimate: ~600–1000 lines (G2 adds a little).
