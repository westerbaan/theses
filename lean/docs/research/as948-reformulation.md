# Is `AlfsenShultzJordanFromDerivations` implied by the literal A–S 9.48?

Research note, 2026-09-26, no Lean edits.  Inputs: Reconstruction.lean:2311-2336
(the Prop), :2765-2800 (`rec121`), short.tex:2225-2237 (REC 121 proof), :1055
(footnote on compressions), review-rec104.md (b2).  I have no copy of the book.
Every A–S statement below is from memory and marked **[unverified]** where it
matters.

## 1. The Prop as stated (Reconstruction.lean:2322)

```lean
def AlfsenShultzJordanFromDerivations : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W],
    IsOUS W → IsBanachOUS W → IsDirectedCompleteOUS W →
    ∀ (ι : Type u) (e : ι → W) (U : ι → W →ₗ[ℝ] W) (c : ι → ι),
      Function.Injective e →
      (∀ i, 0 ≤ e i ∧ e i ≤ ouUnit W) → (∀ i, e (c i) = ouUnit W - e i) →
      (∀ i, (∀ w, 0 ≤ w → 0 ≤ U i w) ∧ U i (ouUnit W) = e i ∧ U i ∘ₗ U i = U i ∧
        U i ∘ₗ U (c i) = 0) →
      (∀ i w, 0 ≤ w → (U i w = 0 ↔ U (c i) w = w)) →
      (∀ i, IsOrderDerivation W (U i - U (c i))) →
      (∀ (w : W) (ε : ℝ), 0 < ε → ∃ l : List (ℝ × ι),
        ousNorm W (w - (l.map fun p => p.1 • e p.2).sum) < ε) →
      ∃ _ : Mul W, JBAlgebra W ∧
        ∀ i w, e i * w = (2⁻¹ : ℝ) • (w + (U i w - U (c i) w))
```
Remarks.  Injectivity of `e` makes `c` involutive (`e (c (c i)) = e i`), so the
iff gives both ker⁺U_i = im⁺U_{ci} and ker⁺U_{ci} = im⁺U_i.  That is the
*primal half* of A–S's bicomplementarity.  There is **no** normality (weak*
continuity), **no** dual/predual, and nothing ties the family to "all
compressions".

## 2. A–S *Geometry* (2003), 9.43 and 9.48, as I remember them  [unverified]

* Standing setting of Ch. 8–9: A order unit space, V base norm space, **A = V\***
  (so A is a dual space and monotone complete), and A, V in **spectral duality**.
  That means every a ∈ A has a unique spectral resolution {e_λ} by projective
  units, where the projective units are the P1 for **compressions** P.  A
  compression is a *normal* positive projection P with a normal P' such that
  ker⁺P = im⁺P' and im⁺P = ker⁺P', plus the matching conditions on V.  The
  lattice of projective units is complete and orthomodular, and the compressions
  are in bijection with the projective units.
* In that setting A–S define the **generalized Jordan product**
  a∘b by integrating p ↦ p∘b against the spectral resolution of a.  In particular p∘b = ½(b + U_p b − U_{p'} b), exactly the Prop's formula.
  The definition is well defined per `a` *because the spectral resolution is
  unique*.
* **9.43** (roughly): if the generalized product is **bilinear**, A is a
  JBW-algebra with that product.  Its proof gives norm continuity, the Jordan
  identity and 0 ≤ a² ≤ 1 for −1 ≤ a ≤ 1.
* **9.48** (roughly): in spectral duality, if for **every** projective unit p the
  map U_p − U_{p'} is an order derivation, then ∘ is bilinear.  So by 9.43, A is
  a JBW-algebra.  The key step is [D_p, D_q]1 = 0.  It uses that commutators of
  order derivations are order derivations (State Spaces 1.114), together with the
  self-adjoint/skew decomposition of order derivations relative to the duality
  ⟨A, V⟩: δ is "self-adjoint" when δ\* preserves V's structure appropriately,
  and a skew order derivation kills 1.
* Conclusion: a **JBW**-algebra, which is stronger than the Prop's "JB-algebra".

## 3. Does literal A–S imply the Prop?  Answer: no, not as stated

### 3a. The Prop quantifies over all W, and most such W lie outside A–S's setting
A dc Banach OUS need not be a dual space.  A monotone complete JB-algebra that is
not JBW, such as a Dixmier algebra C(X) with X extremally disconnected but not
hyperstonean, satisfies every hypothesis of the Prop: take all projections and
U_p = multiplication.  It has no normal states, so it is in spectral duality with
no base norm space.  The Prop's conclusion holds there, since the algebra *is*
JB.  But literal 9.48 says nothing about it.  So literal A–S cannot imply the
Prop *as a ∀W statement*.  At best it implies the restriction to W = V\* in
spectral duality whose family (e, U) is *all* the compressions.
### 3b. Well-definedness of p ↦ p∘w on span{e_i}
This is the heart of the question.
* Reduction (correct, and it is what short.tex:2235 means by "commutativity").
  Put T_i = ½(1 + U_i − U_{ci}), so T_i 1 = e_i.  Suppose the **symmetry**
  T_i e_j = T_j e_i holds for all i, j.  Then for a = Σλ_k e_{i_k} and
  b = Σμ_l e_{j_l},
  Σλ_k T_{i_k} b = ΣΣ λ_k μ_l T_{j_l} e_{i_k} = Σμ_l T_{j_l} a.
  The left side depends on b only as a vector, and the right side on a only as a
  vector.  So (a, b) ↦ a*b is a well-defined bilinear map on span × span.  If
  T_i and T_j do not commute, that does no harm.  The print's phrase "commutativity
  of the T_{p_i} and T_{q_j}" should be read as p*q = q*p, not as [T_p, T_q] = 0,
  which is false in B(H)_sa.
* So well-definedness ⇔ [D_i, D_j]1 = 0 for all i, j.  **The compression axioms
  plus density alone do not give this.**  Even the special case
  e_k = e_i + e_j with e_i ⊥ e_j needs D_k = 1 + D_i + D_j.  In a JB-algebra this
  identity is U_1 = U_p + U_q + U_r + 2ΣU_{·,·}, which is Jordan structure.
  Nothing in the compression axioms forces additivity of U in its projection.
* In A–S, [D_p, D_q]1 = 0 is exactly the content of 9.48.  The argument, as I
  recall it, needs the pairing with V (adjoints δ\*, normality, uniqueness of
  compressions with a given P1).  REC's V_A has none of these established.  So
  **well-definedness is not available without A–S's machinery**, and that
  machinery lives in spectral duality.  `spectral_rep`/`spectral_dense` give
  spectral resolutions inside each commutative bicommutant {a}''.  They say
  nothing about how U_p and U_q interact for non-commuting p and q, which is
  where the content lies.
### 3c. Bridging V_A into A–S's setting: what it would take
To use literal 9.48 in `rec121` one needs all of the following.
1. V_A = V\* for a base norm space V in spectral duality with it.  A candidate is
   V = span of the normal states of V_A.  The effectus is separated by states
   (`separatedByStates`, :288), and in a normal effectus the states are normal,
   so the normal states of V_A do separate.  But "dc OUS + separating normal
   states ⇒ dual space" is Shultz's theorem **for JB-algebras**.  It uses Jordan
   structure, which is circular here.  For a bare OUS I know no such theorem, and
   I suspect it fails.
2. Every A–S compression of V_A is some asrt_p with p sharp (bijection with
   projective units), and each asrt_p is normal.
3. Each a ∈ V_A has an A–S spectral resolution.  REC's `spectral_rep` is close
   to this, but it is phrased in the SEA and not via A–S projective faces.
4. Downgrade JBW → JB.  This is trivial.
Items 1–2 are the real gap.  Item 1 is at research level, not just Lean cost.
### 3d. Is the Prop false?
I found no counterexample.  Classical W = ℓ^∞ and ℝⁿ are rigid: the axioms force
U_i = multiplication by e_i.  The risk is a non-normal "compression" on a
non-dual W, or an exotic non-JB W with such a family.  The hypotheses are strong:
D_i order derivations, dense span, dc.  I cannot settle truth without the book's
9.48 proof, to check whether it uses duality essentially or only for bookkeeping.

## 4. Recommendation

**Keep the Prop, but relabel it honestly.**  Do not claim it is A–S 9.48.
* Docstring: "REC's transplant of the argument of A–S *Geometry* 9.43/9.48
  (short.tex:2229-2237: 'we can copy the argument of Theorem 9.43') to
  directed-complete Banach OUSs without spectral duality.  It is **not implied**
  by the literal theorem: A–S assume A = V\* in spectral duality with normal
  compressions for all projective units.  Its truth is open here."
  This matches the print, which itself only sketches a transplant.
* Optional sharper factorisation, where each piece is closer to a checkable
  claim:
  (H1) *symmetry*: under the Prop's hypotheses, (U_i − U_{ci})e_j = (U_j − U_{cj})e_i.
  This is the A–S 9.48 core.
  (H2) *9.43 transplant*: a family satisfying the hypotheses plus (H1) yields a JB
  product with the given formula.
  Well-definedness on the span, from (H1), is then **provable in Lean** by the
  reduction in 3b, at an estimated 80–150 lines.  So the named black box shrinks
  to (H1) plus continuity, the Jordan identity and a² ≥ 0.
* A faithful restatement of literal 9.48 (A = V\*, base norm V, spectral duality,
  normal bicomplemented compressions for every projective unit ⇒ JBW) is
  possible.  But bridging V_A into it needs item 3c.1, a predual for V_A.  That
  is unproved in the literature for bare OUSs, and its Lean cost is several
  thousand lines (weak\* topology, faces, P-projections) if it is true at all.
  **Not recommended.**
* ERRATA: REC 121's proof is a sketch.  It invokes 9.48 outside its hypotheses
  (no spectral duality is established for V_A), and the well-definedness remark
  should say "symmetry p*q = q*p", not "commutativity of the T_p".
  File this only if a reader would stumble, per the filing standard.  The
  out-of-hypotheses citation probably qualifies.

**Could not verify:** exact numbering and wording of A–S 9.43/9.48.  Whether the compression definition
there includes normality.  Whether the 9.48 proof of [D_p, D_q]1 = 0 uses the
V-pairing essentially.  Whether the Prop is true for all W.

## Review (2026-09-26)

Break-it review; checked against short.tex, Reconstruction.lean, numpy in M_2.

**(A) Scope and non-implication: STANDS in substance, but overclaimed as worded.**
* The Dixmier C(X) example is valid.  X is Stonean, so projections span a dense
  set.  U_p = mult by p, D_p = mult by 2p−1, and e^{tD_p} is positive.  The Prop's
  ∀W does range beyond W = V\* in spectral duality.
* But "literal A–S does not imply the Prop" cannot be shown by an instance where
  the conclusion *holds*.  If both statements are true, one trivially implies the
  other.  The defensible claim is: **no derivation is known, and literal 9.48 does
  not apply as an instance.**  Reword 3a/§4 that way.
* The claim "not derivable from compression axioms + density" (3b) is asserted
  with no countermodel.  It should read "not known to be derivable".  The
  D_k = 1 + D_i + D_j computation is correct: I rechecked it against JB U-operator
  additivity.  It shows the content is Jordan-theoretic, not that it is underivable.
* "Well-definedness ⇔ [D_i,D_j]1 = 0": only ⇐ is shown.  ⇒ does hold, but via the
  Prop's *conclusion* (commutativity).  Well-definedness alone need not give it.

**(B) No easy bridge: STANDS, as a judgement.**  The predual/Shultz-circularity
point is right.  One more premise is unverified: "in a normal effectus the
states are normal".  Also, the bridge must go *both ways* for item 2 (every A–S
compression is an asrt_p).  Both only make the bridge harder.

**(C) "[T_p,T_q] = 0 is false in B(H)_sa, so REC 121's phrase is wrong": the
math STANDS; the erratum is NOT WARRANTED.**
* short.tex:2231 defines T_p := ½(id + asrt_p − asrt_{p⊥}), and T_p 1 = p.  With
  U_p b = pbp this is b ↦ ½(pb+bp).  I checked this numerically.
* :2233: "commutativity of the Jordan product … p*q = q*p … [T_p,T_q]1 = 0".
* short.tex:2235 says: "That this is well-defined follows from the commutativity
  of the T_{p_i} and T_{q_j}."
* Explicit check: p = diag(1,0), q = ½[[1,1],[1,1]].
  - T_pT_q p − T_qT_p p = ⅛[[0,−1],[−1,0]] ≠ 0.
  - [T_p,T_q]1 = T_p q − T_q p = 0.
  Only the "applied to 1" reading is true; no narrower operator reading helps.
* Reader test.  2235 opens "As mentioned above" and points back to 2233, where
  "commutativity" was just defined as [T_p,T_q]1 = 0; :2323 says the T_a need
  not commute ("operator commute").  A reader of §5 does not
  take 2235 as operator commutation.  **Do not file.**  At most, the docstring may
  gloss it as "symmetry T_p q = T_q p".

**(D) Recommendation: the relabelling is SOUND.  H1 as written is BROKEN.**
* §4 states H1 as (U_i − U_{ci})e_j = (U_j − U_{cj})e_i, i.e. D_i e_j = D_j e_i.
  **This is false already in ℝ²**: with commuting p, q, D_p q − D_q p = q − p.
  - In M_2 with the p, q above: D_p q − D_q p = ½[[1,−1],[−1,−1]] ≠ 0.
  - The correct symmetry is T_i e_j = T_j e_i, i.e.
    **D_i e_j + e_j = D_j e_i + e_i**, equivalently [D_i,D_j]1 = 0.  Note
    [D_i,D_j]1 = 2(D_i e_j − D_j e_i − e_i + e_j).
  - As written, H1 is a *false* Prop (the ℝ² model refutes it), so assuming it
    would make rec102/103 vacuous.  Fix it before any Lean.
* "Weaker/more honest": H1 ∧ H2 is **equivalent** to the Prop, not weaker.
  - Prop ⇒ H1 via commutativity of the conclusion.
  - Prop ⇒ H2, since H2 has more hypotheses.
  - H1 ∧ H2 ⇒ Prop, by the Lean bridge.
  The split does not reduce trust.  It only localises it: H1 is the 9.48 core,
  and H2 is the 9.43 transplant.  That is still worth doing for readability.
  Do not sell it as a weakening.
* 80–150 lines for well-definedness on the span: plausible.
* The docstring wording "transplant … without spectral duality; truth open" is
  accurate.  The existing docstring (:2311) already says "no spectral duality",
  but still titles it "Alfsen–Shultz 9.48 (via 9.43)".  Retitle it.

**Correction (2026-09-26, `rec-citations.md`):** as printed, *Geometry* Thm 9.43 (p. 346) is "a spectral K is a JBW normal state space iff T_e f = T_f e" (the symmetry (9.29)), not bilinearity of the product; Thm 9.48 (p. 352) is "K is the normal state space of a JBW-algebra iff K is spectral and elliptic", whose proof gets [P−P′, Q−Q′]1 = 0 and applies 9.43.
