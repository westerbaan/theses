# A–S 9.43 in infinite dimension: the almost-Jordan route (claimed)

Research note, 2026-09-26.  No Lean edits.  Inputs: as943-infinite.md and its Review.
Scratch: `aj-lin.py` (multilinear identity ranks, sympy), `aj-nil.py` (the Review's nil example).
**Everything is claimed**, for adversarial review.  Notation from as943-infinite: `L`, `L̄`
(bounded extension under (i)), `a∘b = L̄(a)b`, `T_i = L(e_i)`, `g(K)` = bounded order derivations.

## 0. Verdict

* **Correction to the brief.**  (K) is *not* supplied by the family.  In as943-infinite §4, (K)
  ("every `[L(v),L(w)]` is a derivation of `∘`") is the statement that the finite-dimensional
  proof gets from the trace form.  In infinite dimension it is open.
* **New (claimed):** given (i), **(K) ⇒ (J) ⇒ (P)**.  The ingredients are:
  (a) (K) is exactly the almost-Jordan / commutative-CD identity (§1, verified by computation);
  (b) `a∘a = 0 ⇒ a = 0`, from order derivations alone, so `(W,∘)` is semiprime (§2);
  (c) Hentzel–Peresi: a semiprime almost-Jordan ring is Jordan (§3; the statement is
  verified only via secondary sources);
  (d) (J) + (i) ⇒ (P), by a Kadison-type argument on the closed subalgebra `C(a)` (§4).
* **Remaining open lemma:** the Prop ⟺ (i) + (K), and (K) reduces to generators:
  > **(K₃)** for all `i, j, k`: `[[T_i,T_j],T_k] = L̄([T_i,T_j] e_k)`.
  A sufficient "naturality" form is given in §5.

## 1. (K) = almost Jordan (verified by computation over ℚ)

* A linear `D` is a derivation of `∘` iff `[D, L_c] = L_{Dc}` for all `c`.  So (K) reads
  `[[L_a,L_b],L_c] = L_{[L_a,L_b]c}`.
* **(K) ⇒ AJ, by hand.**  Take `D = [L_c,L_a]`, so `Da = ca² − a(ac)`.  Apply
  `[D,L_a] = L_{Da}` to `a`.  This gives
  `c a³ − 3 a(a²c) + 2 a(a(ac)) = 0`, i.e. `2((ca)a)a + c a³ = 3(c a²)a`.
  That is Osborn's almost-Jordan identity (AJ).
* **AJ ⇒ (K) (char 0).**  In the free commutative nonassociative algebra, multilinear
  degree 4 (`aj-lin.py`): the 24 instances of (K) span a space of rank 3.  The full
  linearisation of AJ has rank 3, and together they still have rank 3.  So they are the
  **same** multilinear identity, and over ℝ (K) ⟺ AJ.
* This agrees with the literature: Jumaniyozov–Kaygorodov–Khudoyberdiyev (arXiv:2110.12849)
  define CD-algebras by "the commutator of any pair of multiplication operators is a
  derivation".  In the commutative case this reduces to `2((yx)x)x + yx³ = 3(yx²)x`, and
  "commutative CD-algebras [are] also known as … almost-Jordan algebras" (fetched and quoted).
  Other names: Lie triple algebras (Petersson, Math. Z. 97 (1967); Sidorov, Algebra
  and Logic 1981); Osborn, Proc. AMS 16 (1965) 1114–1120.
* The Review's 4-dimensional nil algebra satisfies AJ (residual 1e−14, `aj-nil.py`).  `ℝz` is
  an ideal with `z² = 0`, so it is not semiprime.  This is consistent with §3.

## 2. Semiprimeness from order derivations (claimed; elementary)

**Lemma.**  Assume (i).  For `a ∈ W`: if `a∘a = 0` then `a = 0`.
*Proof.*  `L̄(a)` is a bounded order derivation.  `e^{tL̄(a)}` is the norm limit of
`e^{tL(a_n)} ≥ 0`, as in as943-infinite §3.  Now `L̄(a)1 = a` and `L̄(a)a = 0`, so
`L̄(a)^n 1 = 0` for `n ≥ 2`, and `e^{tL̄(a)}1 = 1 + ta ∈ K` for every `t ∈ ℝ`.  Hence
`±a ≥ −1/|t|` for all `t`, so `±a ∈ K` (K is closed) and `a = 0` (K is proper).  ∎
(For `a ∈ S`, (i) is not needed.)
**Corollary.**  `(W,∘)` has no nonzero ideal `I` with `I∘I = 0`.  More strongly, it has no
nonzero solvable or nilpotent ideals: the last nonzero derived power `J` would satisfy
`J∘J = 0`.  So `(W,∘)` is semiprime under every standard definition of the term.  Note
that `a∘a ≥ 0` is **not** obtained here, and it is not needed.

## 3. Hentzel–Peresi (statement verified via secondary sources; proof not read)

Citation: I. R. Hentzel, L. A. Peresi, *Almost Jordan rings*, Proc. AMS 104 (1988), no. 2,
343–348, doi:10.1090/S0002-9939-1988-0962796-4.  The AMS PDF returned 403, so it was not read.
Secondary quotes, from arXiv:2110.12849 and a search snippet reproducing the abstract:
"any Jordan ring satisfies 2((ax)x)x + a((xx)x) = 3(a(xx))x … this identity along with
commutativity implies the Jordan identity in any semiprime ring … the proof requires
characteristic ≠ 2,3", and "every semiprime almost-Jordan ring is Jordan".
* **Applies here (claimed).**  The theorem is purely ring-theoretic: no unit, no finiteness,
  no topology.  `(W,∘)` is a commutative ℝ-algebra, so 2 and 3 are invertible.  It is AJ by
  §1 once (K) holds on `W`, and semiprime by §2.  Hence **(i) + (K) ⇒ (J)**.
* **Unverified details:** HP's exact definition of "semiprime" and of "characteristic ≠ 2,3"
  (no 2-/3-torsion versus a field).  §2 gives the strongest forms and ℝ has no torsion, so
  either reading is covered.  Before Lean, **read the paper**: in particular, whether "ring"
  assumes associativity of powers or anything else.
* (K) on `W` follows from (K) on `S`.  Given (i), both sides of `[[L̄a,L̄b],L̄c] = L̄([L̄a,L̄b]c)`
  are norm-continuous and trilinear.  Hence (K) ⟺ (K₃) on generators.

## 4. (i) + (J) ⇒ (P) (claimed)

Fix `a ∈ W` and let `C(a)` be the closed subalgebra generated by `1, a`.  Jordan algebras
over ℝ are power-associative [standard, recalled], so `C(a)` is an associative commutative
Banach algebra.  Let `K_a := K ∩ C(a)`.  Then `1` is an order unit for `K_a`, and the order-unit
norm of `(C(a), K_a)` is the restriction of the norm of `W`.
1. For `b ∈ C(a)`, `e^{L̄(b)} ∈ Aut(K)` maps `C(a)` to itself and acts there as multiplication
   by `exp b`.  So `M_{exp b}` is an order automorphism of `K_a`.
2. The orbit argument of as943-infinite §3, run inside `C(a)` with the group
   `{M_{exp b}}`: `b ↦ exp b` has derivative `id` at 0, so the orbit is open.  The Thompson
   metric makes the orbit closed in `int K_a`, and `int K_a` is connected.  Hence
   **`int K_a = exp(C(a))`** and `K_a` is the closure of `exp(C(a))`.
3. `exp b · exp c = exp(b+c)`, and the product is continuous, so **`K_a · K_a ⊆ K_a`**.
4. Take an extreme state `φ` of `K_a` and `0 ≤ p ≤ 1`.  Then `x ↦ φ(px)` and `x ↦ φ((1−p)x)` are
   positive by step 3 and sum to `φ`, so `φ(p·) = φ(p)φ`.  Such `p` span `C(a)`, so `φ` is
   multiplicative (Kadison's argument).
5. Hence `φ(a²) = φ(a)² ∈ [0,1]` whenever `−1 ≤ a ≤ 1`.  In the Archimedean OUS `C(a)`,
   positivity is detected by extreme states (Krein–Milman), so **`0 ≤ a∘a ≤ 1`**, which is (P).  ∎
So **Prop ⟺ (i) + (K) ⟺ (i) + (K₃)** (claimed; ⇒ holds because JB multiplications satisfy (K)).

## 5. What is left: (i) and (K₃)

* **(i)** is unchanged from as943-infinite §2.  It suffices that `D_C` is dense for some `C`.
* **(K₃)** is a statement about triples in the family.  `X := [T_i,T_j]` is a unital order
  derivation, because `g(K)` is a Lie algebra and `X1 = 0`.  So `Y := [X,T_k] − L̄(Xe_k)` is
  also a unital order derivation (`Y1 = Xe_k − Xe_k = 0`), and (K₃) says `Y = 0`.
  Finite dimension gives `Y = 0` through the trace form.  As943-infinite §4 notes that no
  global trace exists here.
* **Sufficient naturality form (claimed reduction).**  Suppose that
  (N') for every A–S compression `P` with projective unit `p` and complement `P'`,
  `L̄(p) = ½(1 + P − P')`.
  Then (K) follows.  For a unital `g ∈ Aut(K)`, `gU_kg⁻¹` is a bicomplementary normalised
  positive projection with projective unit `g e_k`.  If compressions are determined by their
  projective units [A–S, *State spaces* Ch. 7, recalled, unverified], (N') gives
  `g T_k g⁻¹ = L̄(g e_k)`.  By linearity and density, `g L̄(a) g⁻¹ = L̄(ga)`.  Differentiating
  at `g = e^{tX}` gives `[X, L̄a] = L̄(Xa)`, which is (K).  (N') holds in JB-algebras
  (Peirce).  It is automatic when the family is already `G₀`-invariant, e.g. all projective
  units, but not for an arbitrary dense family.
* **No counterexample shape changes.**  A counterexample now needs (α) unbounded `L`, or
  (β) bounded `L` with `(W,∘)` not almost-Jordan.  In case (β), the failure of (K) cannot come from nil
  or nilpotent phenomena, because §2 rules out square-zero elements.

## 6. Claimed, for adversarial review

§1 (K) ⟺ AJ (the computation is verified; the hand derivation of ⇒ should be rechecked);
§2 `a∘a = 0 ⇒ a = 0`; §3 applicability of HP (statement from secondary sources only);
§4 (i)+(J) ⇒ (P); §5 (N') ⇒ (K).
Not claimed: (K₃), (N'), or (i).

## Review (2026-09-26)

Adversarial check.  Re-ran `aj-lin.py` (rank K 3, AJ 3, both 3); rechecked by hand the steps below.
AMS PDF: still Cloudflare-blocked (curl, WebFetch), and so is JSTOR.  zbMATH API: found.

**§1 (K) ⟹ AJ: STANDS.**  With `D = [L_c,L_a]`: `D(a²) = ca³ − a(a²c)`, and
`2a·Da = 2a(ca²) − 2a(a(ac))`, which gives `ca³ − 3a(a²c) + 2a(a(ac)) = 0` as stated.
The derivation criterion `[D,L_c] = L_{Dc}` is correct for a commutative product.
**AJ ⟹ (K): STANDS.**  The rank computation is sound (canonical commutative monomials, all 24
substitutions, full linearisation valid over ℝ).  It is **not load-bearing** for the chain,
though: the chain uses only (K) ⟹ AJ (by hand), and Prop ⟹ (K) comes from Jordan theory.

**§2 `a∘a = 0 ⟹ a = 0`: STANDS.**  For `a ∈ W`, `e^{tL̄(a)}` is a norm limit of order
automorphisms for every `t ∈ ℝ` (as943-infinite §3, reviewed).  So `L̄(a)` is an order derivation.
No "plus a multiple of id" is needed.  The series is exact: `L̄(a)1 = a`, `L̄(a)²1 = a∘a = 0`.
Then `1 + ta ∈ K` for all `t`, so `±a ∈ K` (K is closed), and `a = 0` (K is proper).
The corollary about square-zero, nilpotent and solvable ideals is correct.

**§3 Hentzel–Peresi: STANDS, now with a stronger primary-adjacent source.**  The zbMATH review is
Zbl 0716.17033 (Yu. A. Medvedev), quoted verbatim:
"The authors study commutative rings with identity 2((ax)x)x+a((xx)x)=3(a(xx))x, i.e. almost
Jordan rings.  They show that the ideal of an almost Jordan ring generated by all the values of
the Jordan identity polynomial squares to zero.  This implies that any semiprime almost Jordan
ring is Jordan."
So the real theorem is structural: `I := ideal(Jordan values)` has `I² = 0`.  In `(W,∘)` every
`a ∈ I` then has `a∘a ∈ I∘I = 0`, so `a = 0` by §2.  **The definition of "semiprime" drops out
entirely.**  HP assume only a commutative (nonassociative) ring and char ≠ 2,3 (abstract, via
arXiv:2110.12849).  They assume no unit, no finiteness and no power-associativity.  `(W,∘)` is an
ℝ-algebra, so 2 and 3 are invertible.  Values of the Jordan polynomial are ℝ-homogeneous, so ring
ideals and algebra ideals agree here (and the argument above uses neither).
Remaining caveat: the paper itself is still unread; the char hypothesis rests on the abstract
snippet.  Read it before Lean.

**§4 (i)+(J) ⟹ (P): STANDS.**  `C(a)` is associative (power-associativity, closed up by
boundedness of `∘`); order-unit norm and Thompson data restrict (`λ1 ± x`, `λy − x` stay in `C(a)`);
`e^{L̄(b)}|_{C(a)} = M_{exp b}` with positive inverse; orbit argument as in as943-infinite §3;
`K_a = cl int K_a` gives `K_a·K_a ⊆ K_a`; Kadison (`p ∈ [0,1]` span, extreme ⇒ multiplicative)
and Hahn–Banach + Krein–Milman give `0 ≤ a² ≤ 1`.  Step 2 is heavier than needed but correct.

**§3/§5 (K) ⟺ (K₃): STANDS.**  Both sides are trilinear and norm-continuous under (i), and
`span{e_i}` is dense.  `Y` is a unital order derivation: `X1 = T_ie_j − T_je_i = 0`, since
`L(a)b = L(b)a`.  The bounded order derivations form a norm-closed Lie algebra, so `L̄(Xe_k)`
belongs to it.
**(N') ⟹ (K): STANDS, and it is simpler than written.**  `gU_kg⁻¹` (g a unital order
automorphism) is a normalised positive bicomplementary projection with complement `gU_{ck}g⁻¹`
and projective unit `ge_k`.  Applying (N') to it gives `gT_kg⁻¹ = L̄(ge_k)` **directly**.
The A–S fact "a compression is determined by its projective unit" is **not needed** for this
implication.  It matters only for showing that (N') holds in JB-algebras, where every compression
is some `U_p` [A–S, unverified here], and then Peirce gives `½(1+P₁−P₀) = L(p)`.  Differentiating
at `e^{tX}` in fact gives `[X,L̄a] = L̄(Xa)` for **every** unital `X ∈ g(K)`, which is stronger
than (K).  (N') itself is unproved and not claimed; it is flagged correctly.

**Overall: the chain (i) + (K) ⟹ (J) ⟹ (P) ⟹ Prop is sound**, modulo reading HP's paper
(statement confirmed by the zbMATH review).  The converse holds by §4 of as943-infinite plus
"[L_a,L_b] ∈ Der" in Jordan algebras.  So **Prop ⟺ (i) + (K₃) STANDS.**
Fixes: (1) §3 cite Zbl 0716.17033, use the `I² = 0` form, drop the "unverified details" bullet;
(2) §5 drop A–S uniqueness from (N') ⟹ (K); (3) §1 mark the rank computation not load-bearing.
Open, as the note says: (i) and (K₃)/(N').
