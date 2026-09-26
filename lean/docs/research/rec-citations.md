# REC citation check: the named hypotheses against their sources

Checked 2026-09-26 against: Google Books snippets of A–S *Geometry* (70lV9A2leEUC) and *State spaces*
(j43hBwAAQBAJ); the free H-O–S PDF (folk.ntnu.no/hanche/joa/joa-m.pdf, pp. 155–157); arXiv 1803.11139 v1–v3 sources.

Shultz 1979 (Elsevier, 403) was checked only via two secondary citations. The print's own citations (short.tex) give the same numbers as the Lean, except where noted.

## 1. `AlfsenShultzFourExchangeable` (REC 132): VERIFIED
A–S *Geometry of State Spaces of Operator Algebras* (2003), Ch. 4 §"Representations of JBW-factors
as JW-algebras", p. 105 (quoted from the snippet):
> **4.4. Lemma.** If M is a JBW-algebra in which the identity is the sum of n projections
> (4 ≤ n ≤ ∞) exchangeable pairwise by symmetries, then M is a JW-algebra.

The proof reduces n = ∞ to four exchangeable projections (Cor. 3.11), then uses Thm 3.27 and Lemma 4.3.
Theorem 4.5, which follows it, says every JBW-factor other than H₃(𝕆) is JW.
- Label matches short.tex:2377 and Monoidal.lean:274. The Lean statement (Monoidal.lean:279) is faithful and weaker:
  - it covers finite n ≥ 4 only (A–S also allow n = ∞);
  - it adds p_i ≠ 0 and pairwise orthogonality, both automatic or harmless;
  - "exchangeable" is rendered as `jQ s (p i) = p j` with `IsSymmetry s`, which is A–S's U_s p = q.
- The notes' alternative guess "Thm 7.x" is wrong. Chapter 7 is "General compressions".

## 2a. `HancheOlsenStormerDecomposition` (REC 52): VERIFIED
H-O–S *Jordan Operator Algebras* (1984), p. 156:
> **7.2.7. Theorem.** Let M be a JBW algebra. Then M can be uniquely decomposed as a direct sum
> M = M_ex ⊕ M_sp, where M_sp is a JW algebra and M_ex is a purely exceptional JBW algebra.

- 7.2.1 (p. 155) defines "purely exceptional": no nonzero homomorphism into a JC algebra.
- Remark 7.2.8 (p. 156–157) adds that M_ex = ker ψ for ψ : M → W*(M).
- 7.2.3 is the JB-algebra ideal version. Arhancet (arXiv 2608.14231) cites 7.2.3 in a
  commented-out line, but 7.2.7 is the JBW statement, as the print uses it.
- 7.2.7 does **not** contain the C(X, H₃(𝕆)) description. A–S *Geometry* Thm 4.23 (p. 110–112) is the same decomposition, if an alternative citation is wanted.
- The Lean form (Monoidal.lean:296) matches. review-rec136 already vetted the central-idempotent rendering.

## 2b. `ShultzExceptionalStructure` (REC 55): number CORRECTED (VERIFIED via secondary sources)
The result is Shultz, J. Funct. Anal. 31 (1979) 360–376, **Theorem 3.9** (p. 374). Two independent citations give this number:
- Arhancet, arXiv 2608.14231: "by [Shu79, Theorem 3.9 p. 374] or [AlS03, Theorem 4.23 p. 112] … A_exp …
  isomorphic to L^∞_ℝ(Ω, H₃(𝕆))".
- arXiv 2509.03213: "It follows from [Shultz79, Theorem 3.9] … every exceptional JBW*-algebra … C(K, H₃(𝕆^ℂ)),
  K hyperStonean".
The print (short.tex:948) cites Shultz without a number, and the Lean content matches it.

**Error:** Monoidal.lean:305–306 also attributes REC 55 to "Hanche-Olsen–Størmer Thm 7.2.7"; 7.2.7 is only the decomposition.
review-rec136.md:35–36 says "(also H-O–S 7.2.7, second half)". 7.2.7 has no second half.

## 3. Alfsen–Shultz order-derivation numbers: all VERIFIED
*State Spaces of Operator Algebras* (2001), §"Order derivations", pp. 55–61:
- **(1.82)** is a *displayed equation* on p. 55, not a numbered result. Corollary 1.82 on p. 41 is unrelated
  (a C_ℝ(X) characterisation). The equation reads: "for an invertible operator T on a linear space A ordered by a cone A⁺, (1.82) T ≥ 0 ⟺ T⁻¹ maps A∖A⁺ into itself".
  Pp. 56–57 apply it to the resolvent (1 − λδ)⁻¹. So "Eq. (1.82)" (short.tex:2187) is right.
  Resolvent.lean:160 states exactly this, with T⁻¹ = 1 − λB.
- **1.106 Theorem** (p. 56): "Let A be a real Banach space ordered by a closed cone A⁺ with the nearest
  point property, and δ bounded. TFAE: (i) e^{tδ} ≥ 0 ∀t > 0; (ii) …; (iii) resolvent positive".
  `AlfsenShultzResolventCriterion` is (1.82) plus (iii)⇒(i) applied to ±δ, and that step does not need
  the nearest-point property. The Lean description (Reconstruction.lean:2316–2322) is accurate.
- **1.108 Proposition** (p. 58): "Let A be a complete order unit space, δ bounded. TFAE: (i) δ is an order
  derivation; (ii) if x ∈ A⁺, 0 ≤ σ ∈ A* and σ(x) = 0 then σ(δx) = 0". It is proved by applying 1.106 to ±δ.
  The Lean version with states (Reconstruction.lean:2303) is equivalent by scaling.
- **1.114 Proposition** (p. 60): "The set D(A) of order derivations of a complete order unit space A is a
  real linear space …". The proof on p. 61 shows D(A) is closed under Lie brackets
  ("to show that D(A) is closed under Lie brackets, it suffices to show [δ₁, δ₂] is an order derivation").
  This matches short.tex:2233 and the notes.
- *Geometry* **9.43 Theorem** (p. 346): "A spectral convex set K is the normal state space of a
  JBW-algebra iff (9.29) T_e f = T_f e for all pairs e, f ∈ A = A_b(K)…".
  The criterion is *symmetry on projective units*. as948-reformulation.md §2 recalls it as "if the
  generalized product is bilinear", which is close but not the printed hypothesis.
- *Geometry* **9.48 Theorem** (p. 352): "A convex set K is affinely isomorphic to the normal state space
  of a JBW-algebra iff K is spectral and elliptic".
  The proof shows [P − P′, Q − Q′]1 = 0, displayed as (9.43) on p. 352, "which by Theorem 9.43 will
  complete the proof", using that P − P′ is an order derivation.
  Van de Wetering (arXiv 1803.11139v3, Thm 4) independently cites the same 1.108 and 9.48.

## 4. `WeteringStateOrderLemma` (REC 119): number VERIFIED, title CORRECTED
arXiv 1803.11139 has three versions:
v1 (2018-03) is "Sequential Measurement Characterises Quantum Theory"; v2 (2018-10) and v3 (2020-12) are
"**Sequential Product Spaces are Jordan Algebras**", published in J. Math. Phys. 60, 062201 (2019). This is the bib entry `wetering2018sequential` (short.bbl:467).

The Lean's "*Sequential measurement characterises finite-dimensional quantum theory*" is not the title of any version.

**Prop 46 exists only in v3**, in §"Infinite-dimensional sequential product spaces".
- Numbering: one counter is shared by Proposition, Lemma, Corollary, Example and Remark; Theorems and
  Definitions have their own counters. Counting the uncommented environments gives Prop 45 at
  full_article.tex:826 and Prop 46 at :838.
  v1/v2 have no such proposition (counter stops at 41).

> **Proposition [46].** Suppose the sequential product is comprehensive and quadratic, then for any a ≥ 0
> the following implication holds for any σ-normal ω: if ω(a) = 0 then ω(p & a) = ω(p^⊥ & a) for any
> sharp effect p.

Prop 45 is the sharp-q case (via Lemma 44). Prop 46 extends it to simple a by linearity, then to all
a ≥ 0 by suprema, which uses σ-normality of ω.

Compared with REC 119: same conclusion. The differences: (i) vdW's states are σ-normal states of a σ-sequential product space, while REC's are the effectus's internal states; (ii) vdW's axiom is "comprehensive" (ω(q) = 1 ⇒ ω(q & p) = ω(p)), which the print calls "compressive"/"compressible".

The print's "exactly as … Proposition 46" is therefore the right pointer. The transfer to internal
states is the unprinted step the Lean already records.

## 5. Fixes needed (docstrings / notes; no Lean statement changes)
1. Monoidal.lean:305–306.
   Old: "Shultz 1979,\nHanche-Olsen–Størmer Thm 7.2.7)"
   New: "Shultz 1979, Thm 3.9\n(J. Funct. Anal. 31, p. 374); H-O–S 7.2.7 is only the decomposition, REC 52)".
2. Monoidal.lean:24. Old: "REC 55 (Shultz 1979)". New: "REC 55 (Shultz 1979, Thm 3.9)".
3. Reconstruction.lean:2553–2555.
   Old: "van de\nWetering 2018, *Sequential measurement characterises finite-dimensional quantum\ntheory*, Prop. 46, which is about the states of a compressible quadratic SEA"
   New: "van de\nWetering, *Sequential product spaces are Jordan algebras* (J. Math. Phys. 60, 2019;\narXiv:1803.11139v3), Prop. 46, which is about the σ-normal states of a σ-sequential product space\nwith a comprehensive quadratic product".
4. Reconstruction.lean:23. Old: "van de Wetering 2018, Prop. 46". New: "van de Wetering 2019 (arXiv:1803.11139v3), Prop. 46".
5. Algebras.lean:459.
   Old: "*Sequential measurement characterises quantum theory* (2018),\nTheorem 4" → New: "*Sequential product spaces are Jordan algebras* (2019;\narXiv:1803.11139v3), Theorem 4".
   (Thm 4 there is "σ-sequential product space, comprehensive + quadratic ⇒ σ-complete JB-algebra".)
6. PLAN.md:51. Old: "van de Wetering 2018 (*Sequential measurement characterises…*) Prop 46".
   New: "van de Wetering 2019 (*Sequential product spaces are Jordan algebras*, arXiv v3) Prop 46".
7. review-rec136.md:35–36. Old: "(also\n  H-O–S 7.2.7, second half)". New: "(Thm 3.9; A–S *Geometry* 4.23 for the decomposition)".
8. review-rec136.md:48–50. Old: "I could not check offline that A–S *Geometry* Lemma 4.4 is the right label. …".
   New: "A–S *Geometry* Lemma 4.4 (p. 105) verified: n projections, 4 ≤ n ≤ ∞, exchangeable pairwise ⇒ JW (rec-citations.md)".
9. README.md:37. Old: "(the A–S Lemma 4.4 label for REC 132 unverified offline)". New: "(A–S Lemma 4.4 label verified, rec-citations.md)".
10. as948-lemmaM.md:34, :61–62, :168–169. Drop "[unverified numbering]" and "numbering … still unverified":
    1.108 and 1.114 are verified.
11. as948-reformulation.md:33–47 (optional).
    9.43's hypothesis is "(9.29) T_e f = T_f e" (symmetry), not "bilinear"; 9.48 is "K spectral and elliptic ⟺ normal state space of a JBW-algebra".

No change needed: Monoidal.lean:23/28/274/287, Reconstruction.lean:2303/2316–2322/2332, Resolvent.lean, JordanSymmetry.lean, Reconstruction2.lean:53, PLAN.md:52/54/57/60.
