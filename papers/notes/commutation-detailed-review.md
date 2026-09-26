# Referee report: `commutation-detailed.tex`

**Verdict: ready after the listed fixes.** I checked every displayed equation and inequality by hand. The mathematics is correct throughout: I found no sign, constant, substitution, inequality-direction or positivity error. The problems are one wrong citation, one broken line of source, one false tolerance claim, and some over-claims or missing justifications in the framing.

Tally: **2 errors, 4 gaps, 4 typos, 3 style.**

## What was checked (all passed)

- **Part I.** (J) is the λμν-coefficient with factor 2; (II) is read off correctly as an operator in `a`. Both instances in Lemma 3 (derivation) cancel in pairs as stated. Lemma 4 (D at A): the ¼ and ½ agree with `U_x y² − U_y x²`.
- **Lemma 6 (intertwining).** The expansions of `[P,U_x]`, `DU_x`, `U_xD` and the coefficient table (`XPX` −4+4, `PX²` 4−2, `XQY` −2+1+1, `QYX` 2−1, `YQX` −1+1) are right. I re-checked (Kid) as a non-commutative polynomial identity in sympy (`revnote-checks.py`). Re-running `note-verify.py` gives JK (hand) = JK (Lean 10) = True, coefficients [-1,-2,2,1/3,1/3,1,-1].
- **Part II.** `MU+UN = 2([L_A,U]+DU+UD)`; the splitting is legitimate because `[D,L_A]=L_{D(A)}=0`; evaluation at 1 and the bound (Lemma 7 at time −t) are right. Numerically `Exp(tM)U_xExp(tN)=U_x` holds for random `x,y` in Sym₄ with no hypothesis, confirming the signs in Lemma 6.
- **Part III.** Gap lemma: Step 1 sign of `2τ(α−t)` right; Step 3 moves past each other only `U`'s of elements of `C(h)` (never needs `L_G` to commute with `L_{G²}`); Step 4 needs τ>0, t≥β; the constant `3C‖f‖‖k‖²e^{−2τ(β−α)}` and the τ→∞ direction are right. Prop. 10: α=s+1/(m+1) < β=s+2/(m+1), `1−p ≤ f_m(h)`, Fact 6 applied twice with the right roles, `σ_n ≤ (n+1)ρ`, normality used only for r=√u ≥ 0.
- **Part V.** (y+λ,a) trick: `W_{x_λ,h_λ}(τ)=W_{x_λ,A_λ}(τ/λ)` and λ→∞ gives `h_λ→a`. Lemma 15 (SQ) has the right roles.
- **Part VI.** VI.1 cancellations and both consequences; VI.2 (t=∓s direction); VI.3 (averaging a±b); VI.4 (x′≥0 makes e≥0, `U_{P,R}1=P∘R=0`, `U_ce=U_PU_{x'}U_PU_Rx'=0`, (G) in both orders). VI.5: `Δ=½(U_{1,g²}−U_g)`; supports φ⊂[c,c+2ε], ψ⊂[c−2ε,c+4ε], ℓo=0 on t≥c−ε, hi=0 on t≤c+3ε; |t−μ| ≤ ε resp. 3ε; ¼(27+3)ε²+¼(9+9)ε² = 12ε²; f₀=1 (ε≤1), f_N=0 (c_N ≥ R₀+1), N=Mn pieces, total 12M‖x‖/n → 0. VI.6: `δ^{m+1}(TY)=Tδ^{m+1}Y+(m+1)Dδ^mY`, `δⁿ(Tⁿ)=n!Dⁿ`. VI.7: growth `Be^{2√(K|w|)}`; after z↦z², G is real on both axes, order 1 < 2 = π/(π/2), Phragmén–Lindelöf per quadrant, then Liouville. VI.8 odd-n step right.
- **HOS section numbers,** checked against the authors' free PDF (hanche.folk.ntnu.no/joa/joa-m.pdf, pp. vii–viii): §2.4 Jordan algebras (FF is 2.4.18), §2.6 Peirce decomposition, §3.1 Definition of JB algebras, §3.2 Spectral theory, §3.3 Order structure, §4.1 Topological properties, §4.2 Projections in JBW algebras. 3.3.6 read verbatim ("If b≥0 then {aba}≥0"). HOS 3.2.7 states the same constant `‖U_a x‖≤3‖a‖²‖x‖`.
- **Lean.** All 44 identifiers in "Formalised as" exist (`opComm_of_sprojs`, `jbw_mul_mem` in `SEA/JBCommThm.lean`; `sq_eq_zero_comm`, `jQ_isLUB` in `SEA/JBAllSEA.lean`; `ph_of_jQ_one_sub` in `SEA/JBSeqComm.lean`). The route matches the file headers (JBW `(y+λ,a)` step, 12ε² in `piece_bound`, `ks_norm`, `eq_zero_of_bounded_group`, `gap_zero_s` with sign s). Nothing false is said about the Lean proof, apart from the wording in G1.

## Errors

**E1 — Bibliography, `\bibitem{vdW}` (l. 790–791). Error.**
- arXiv:2004.12749 is a different paper: A. Westerbaan, B. Westerbaan and J. van de Wetering, *The three types of normal sequential effect algebras*, Quantum 4 (2020) 378.
- The paper cited, van de Wetering's *Commutativity in Jordan operator algebras*, is arXiv:1912.01903 (J. Pure Appl. Algebra 224(11), 2020).
- **Fix:** replace the id with 1912.01903 and add the JPAA reference.
- The same wrong id appears in the headers of `JBContPeirce.lean` and `JBCommJB.lean`. I have not edited those; flagged for the author.

**E2 — "Verification", l. 763–764. Error (false as stated).**
- The note claims residuals ≤10⁻¹³ on Sym₅(ℝ).
- Re-running `note-verify.py` gives `swap n=1` = 2.84e-13 on Sym₅; the fundamental formula is 2.1e-14. The Albert residuals, max 4.4e-11, are within the stated 5e-11.
- **Fix:** say "≤ 3·10⁻¹³, resp. ≤ 5·10⁻¹¹", or "≤ 10⁻¹⁰" for both.

## Gaps

**G1 — Abstract, l. 35–36 ("No trace, no Shirshov–Cohn or Macdonald theorem … all algebra comes from the linearised Jordan identity"). Gap / over-claim.**
- As a statement about *this note*, it is false:
  - Fact 5 (fundamental formula, HOS §2.4) is proved in HOS through Macdonald's theorem.
  - Fact 4 (positivity, HOS 3.3.6) is proved in HOS through identity 2.4.17.
- The Remark after Fact 5 (l. 113–121) gives a Macdonald-free route for the fundamental formula only, not for positivity.
- **Fix:** say "The formalisation uses no trace, Macdonald or Shirshov–Cohn theorem; beyond the standard facts of §2, all algebra comes from (J)". Then add one sentence to the Remark on positivity, following `JBMacdonald.lean` steps 5–6:
  - `Exp(tL_h)≥0` by the resolvent/state argument;
  - hence U_c≥0 for c≥0;
  - then the swap trick `x·p(x)=U_aU_c p(y)`.

**G2 — l. 57–58, "the converse is immediate, since operator-commuting elements generate an associative subalgebra". Gap.**
- For JB-algebras that fact is a theorem of van de Wetering (1912.01903), not something immediate.
- The converse also needs √b | a, not only a | b.
- **Fix:** "Conversely, if b∈comm(a) then √a|b, and b|a gives bⁿ|a for all n by the powers argument of VI.8, hence √b|a. By Fact 3 both sides then equal a∘b."

**G3 — Fact 7 (JBW), l. 161–177. Gap.** Two items are cited to HOS §4.1–4.2 but are not stated there in this form:
- (i) The construction `π_ρ = sup σ_n(h)` together with the approximation (specapprox).
- (ii) "z operator-commutes with the supremum."

**Fix:**
- For (ii), add one line: the product is separately σ-weakly continuous and monotone limits are σ-weak. Alternatively, cite the Lean argument `opComm_of_isLUB` (JBCommThm §1), which works for directed suprema in any JB-algebra: `N L_v = U_{(N+v)/2} − U_{(N−v)/2}`.
- For (i), give the three-line proof:
  - c = −‖h‖ and m = ⌈2‖h‖/δ⌉+1;
  - in the associative JBW-subalgebra generated by h, the approximant takes the value −‖h‖ + δ·#{k≥1 : kδ−‖h‖ < t}, which lies in (t−δ, t].
  - I checked this numerically in `revnote-checks.py`.

**G4 — Remark after the JB proof, l. 751–752 ("…a convex sequential effect algebra, normal when 𝒜 is JBW"). Gap.**
- The remaining SEA axioms and normality are neither proved nor referenced.
- **Fix:** cite van de Wetering (1912.01903) for the reduction to comm/mul_mem, and HOS 4.1 or `sea16_jbw_of_seqComm` for normality.

## Typos

**T1 — l. 761. Typo (breaks the output).** The source contains `Lemma~<CR>ef{lem:2}`: a literal carriage return replaced the `\r` of `\ref`. The PDF prints "Lemma eflem:2". **Fix:** `Lemma~\ref{lem:2}`.

**T2 — VI.2, l. 600.** `U_{1+tc} = 1 + 2tL_c + t²U_c` should use the identity operator I, not the element 1: write `I + 2tL_c + t²U_c`.

**T3 — VI.4, l. 624.** "by VI.1 (with r²≥0 and pr²=0)" covers only the `L_{R²}` term. The `U_PU_R(1)` term uses the first bullet with r≥0 and pr=0. **Fix:** cite both bullets.

**T4 — VI.7, l. 717.** "grows at most like exp(c|z|¹)": the constant c is undefined, and the letter is already taken. **Fix:** "|G(z)| ≤ B e^{2√K|z|}, of order 1 < 2".

## Style

**S1 — hyperref.** pdflatex warns `destination with the same identifier (name{equation.2})`, caused by `\tag{J}`/`\tag{II}` together with numbered equations, so links may land on the wrong place. **Fix:** give (J) and (II) `\label`s and use `\eqref`, or load hyperref with `hypertexnames=false`.

**S2 — Overloaded letters.** Rename locally, e.g. use `𝒬, 𝒫` in Lemma 6 and `𝔇` in VI.6. The overloads are:
- Q is `L_{x²}` in Lemma 6 but `L_A` in Proposition 8 (the flow).
- P is a Peirce projection, `L_A`, and `p(h)`.
- R is an instance of (II) and also `r(h)`.
- K is an operator in Lemma 6 and a constant in VI.6.
- M is `m(h)`, the operator `2D+2Q`, and the integer in VI.5.
- G is `g(h)`, the hypothesis (G), and the entire function in VI.7.
- D is redefined in VI.6.

**S3 — Minor simplifications and citations.**
- VI.1, first bullet: this is just (M0), `U_{rp}=U_pU_r`; there is no need for (Mb).
- Proposition 13 (the (y+λ,a) trick): rescaling to h_λ is unnecessary for the powers step, since `A_λⁿ|y` gives `h_λⁿ|y` directly. It is harmless; keep it if it mirrors the Lean.
- Fact 5: `U_{e^h}=Exp(2L_h)` is not in HOS §2.4. Point to the Remark instead.
- Fact 1: consider citing HOS 3.2.7 for the constant 3.

## Reproduction

- The author's `note-verify.py` re-runs with all identities True; the residuals are as listed under E2.
- My own checks are in the scratchpad file `revnote-checks.py`: (Kid) symbolically, Lemma 6 and the flow invariance numerically, `U_{e^h}=Exp(2L_h)`, `U_{a,c}b`, the VI.5 display and supports, the Peirce projection sum, and (specapprox).
- My compile of the note in a scratch directory gives 10 pages. There are no undefined references; the only warnings are the duplicate-destination warnings in S1.
