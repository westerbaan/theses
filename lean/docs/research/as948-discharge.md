# Can REC derive [D_p, D_q]1 = 0 itself?  (as948 discharge attempt)

Research note, 2026-09-26.  No Lean edits.  Inputs: short.tex:2150-2237 (REC 119-121),
Reconstruction.lean:2311-2336 (the Prop), :2448-2475 (`Uop`/`Dop`), :2520 (REC 119 =
named hypothesis `WeteringStateOrderLemma`), :620 (`comp_asrtS_of`),
as948-reformulation.md with its Review, review-rec104.md.  Numerics: numpy on
random complex projections in M_4 (scratch script, all checks below pass).

Notation.  For a predicate b, U_p b := p & b = b ∘ asrt_p.  This extends linearly to
V_A (`Uop`).  D_p := U_p − U_{p⊥} and T_p := ½(1 + D_p).  A state ω acts by
ω(x) := x ∘ ω.  In B(H)_sa, p & b = pbp.

## 1. What [D_p, D_q]1 = 0 says.  The brief's formula is wrong

The brief's step "p&q + p⊥&q = q" is **false** unless p and q commute (Gudder:
for sharp p, b = p&b + p⊥&b iff p | b).  In B(H): pqp + p⊥qp⊥ = q − (pq + qp − 2pqp).
Numerics confirm it fails.  So [D_p, D_q]1 ≠ 2(p&q − q&p).  That would also be the
wrong target: pqp ≠ qpq in B(H), yet the symmetry holds there.

Correct computation (D_r 1 = 2r − 1):

    [D_p, D_q]1 = D_p(2q−1) − D_q(2p−1) = 2(D_p q + q − D_q p − p) = 4(T_p q − T_q p).

So the symmetry is **T_p q = T_q p**, i.e.

    (S)   q + p&q − p⊥&q  =  p + q&p − q⊥&p.

In B(H) both sides equal pq + qp; numerics confirm.  This is the review's
corrected H1 (D_i e_j + e_j = D_j e_i + e_i), stated in REC's own terms.

## 2. Peirce splitting of (S): two of three components follow from REC 119 (claimed)

Put R_p := 1 − U_p − U_{p⊥}.  From U_p² = U_p and U_p U_{p⊥} = U_{p⊥} U_p = 0 (the
Prop's hypotheses, supplied at rec121):
* 1 = U_p + U_{p⊥} + R_p are complementary idempotents;
* D_p = diag(1, −1, 0) on this splitting;
* U_p T_p = U_p, U_{p⊥} T_p = 0, and R_p T_p = ½ R_p.

Let x := T_p q − T_q p.  Then (S) ⇔ x = 0 ⇔ U_p x = 0 ∧ U_{p⊥} x = 0 ∧ R_p x = 0.

**Lemma A (claimed).**  For sharp p, q:  p⊥&(q&p) = p⊥&(q⊥&p).
Proof.  Let ω be any state and ω' := asrt_{p⊥} ∘ ω.
* Then p ∘ ω' = (p⊥&p) ∘ ω = 0, because p⊥&p = 0 for sharp p.
* REC 119, with sharp predicate q, a := p and state ω': (q&p) ∘ ω' = (q⊥&p) ∘ ω'.
  That is, (p⊥&(q&p)) ∘ ω = (p⊥&(q⊥&p)) ∘ ω.
* States separate predicates (`separatedByStates`), so the two predicates are equal. ∎

**Lemma B (claimed).**  p&(q⊥&p) = p − 2 p&q + p&(q&p) in V_A.
Proof.
* Apply Lemma A to the sharp predicate p⊥ (with p⊥⊥ = p): p&(q&p⊥) = p&(q⊥&p⊥).
* Expand with S1 additivity: q&p⊥ = q − q&p and q⊥&p⊥ = q⊥ − q⊥&p.
* Also p&q⊥ = p − p&q.
* Rearrange linearly in V_A (U_p is linear). ∎

**Corner components (claimed).**
* U_{p⊥} x = 0 − ½(U_{p⊥}p + U_{p⊥}U_q p − U_{p⊥}U_{q⊥} p) = 0.
  This uses U_{p⊥}p = 0 and Lemma A.
* U_p x = U_p q − ½(p + U_pU_q p − U_pU_{q⊥} p) = U_p q − U_p q = 0, by Lemma B.
* Swapping p ↔ q (which sends x ↦ −x) gives U_q x = U_{q⊥} x = 0.

So **x lies in W½(p) ∩ W½(q)**, the joint Peirce-½ space.  Every step uses only:
* REC 119, which is already a hypothesis of rec121 (`h119`);
* separation by states;
* SEA axiom S1;
* p⊥&p = 0;
* the compression identities that rec121 already proves.

Each step is a few lines in Lean.  `comp_asrtS_of` is not even needed.

## 3. The remaining component is the whole difficulty

**Missing lemma M.**  For sharp p, q ∈ Pred(A): R_p(T_p q − T_q p) = 0.
Given §2, M is equivalent to (S).

**Why the corner facts cannot be enough.**  In M_2(ℂ)_sa, and generically in M_n,
y := i[p, q] ≠ 0 satisfies U_p y = U_{p⊥} y = U_q y = U_{q⊥} y = 0 (numerics:
‖y‖ = 0.62 on the test pair).  So the "pseudo-products"
p ⋆ q = ½(pq + qp) + c·i[p, q] agree with every corner of p and of q for every c.
Any proof of M must see the off-diagonal (Peirce-½) part of q relative to p.

REC's state-side tools do not see that part:
* REC 119 only speaks about states that vanish on a predicate.
* A state with ω(p) = 0 or ω(p⊥) = 0 factors through asrt_{p⊥} or asrt_p, and
  asrt kills W½.
* I tried the order-derivation condition for δ := [D_p, D_q] (A–S 1.114: an order
  derivation), which says ω(a) = 0 ⇒ ω(δa) = 0.  Choosing a ∈ {p, p⊥, q, q⊥} and ω
  in a corner only re-derives Lemmas A and B.  For instance, a = p⊥ with ω
  supported on p gives U_p D_q p⊥ = 0, which is Lemma B.  This condition never
  evaluates δ1 at a state that is off both corners.

**Other routes tried, none closes M:**
* **†-structure.**  asrt_q ∘ asrt_p is pure with dagger asrt_p ∘ asrt_q.  So
  asrt_p asrt_q asrt_p is †-positive.  By uniqueness of asrt, it equals
  asrt_{p&(q&p)} (claimed, fundamental-formula instance; worth recording).  But
  this lives entirely in the p-corner (image ⊆ im U_p) and says nothing about R_p.
* **An inner product making D_p self-adjoint.**  With one, [D_p, D_q] would be
  skew-adjoint, and a skew order derivation fixes the unit on a self-dual cone
  (the Koecher–Vinberg route).  REC's dagger acts on maps, not on V_A.  Without
  a trace or pure states there is no pairing on V_A.  REC has no atoms in general
  (type III).
* **Additivity of T on orthogonal sums** (T_{p+r} = T_p + T_r for p ⊥ r, which
  would reduce to spectral data).  Not available: it is the Jordan content itself
  (Review of as948-reformulation, (A)).
* **Rigidity.**  In B(H), a positive idempotent U with U1 = p and the kernel/image
  conditions must be X ↦ pXp.  An off-diagonal term N is killed by positivity:
  |N(c)| ≲ √ε against pbp = ε.  So *inside* B(H) no twisted model exists, and a
  counter-model needs a non-Jordan V_A.  I found none.  By A–S 9.48 (as recalled
  [unverified]), none exists in spectral duality.  So a counterexample to M would
  also be a counterexample to REC Thm 102 outside spectral duality.

**Verdict: (c) open.**
* The half of the symmetry that REC's cited tools actually support (the corners)
  is derivable (claimed).
* The half that carries the Jordan content (Peirce-½, the i[p, q] direction) is
  not derivable from anything REC states.
* REC 121's proof defers exactly this to A–S 9.48, whose proof (as recalled)
  needs the V-pairing, which REC lacks.
* This is a real gap in the print's argument, not just a missing citation detail.
  Whether the *statement* fails is unknown: no counter-model was found, and in
  finite dimension the reconstruction is expected to hold by a different route
  (van de Wetering's homogeneity/self-duality argument [unverified]).

## 4. Consequences for the Lean Prop

* **Cannot be removed.**  M is open, and the 9.43 transplant is untouched:
  continuity of the product, the Jordan identity, and 0 ≤ a² ≤ 1.
* **Can be localised further (optional, a restatement job).**  Split the Prop into:
  * **(M)**, stated in REC's own terms:
    ∀ sharp p q : Pred A, R_p(T_p q − T_q p) = 0 in V_A.
    Or, for the abstract Prop: ∀ i j, (1 − U_i − U_{ci})(T_i e_j − T_j e_i) = 0.
  * **(H2)**, the 9.43 transplant.
  * Then the corner components (§2, from h119, about 60–100 Lean lines) and
    well-definedness/bilinearity on the span (about 100 lines, per the review)
    become theorems.
* This is a genuine but **small** weakening.  (M) alone is strictly less than H1
  as an assumption shape, but only modulo h119, which is itself a named hypothesis
  (REC 119, `WeteringStateOrderLemma`).  So the trust base goes from
  {h119, H1, H2} to {h119, M, H2}.  Worth it only if the §2.1 alignment pass
  wants the gap stated precisely.
* **Caveat for any abstract version.**  Lemma A uses REC 119 and state separation.
  The abstract Prop quantifies over bare W without states.  So the abstract (M)
  must keep the full symmetry, or add a state-lemma hypothesis in the style of
  REC 119.  The REC-specific form avoids this.
* **Errata.**  "p&q + p⊥&q = q" does not appear in the print, so there is nothing
  to file.  The print's "these facts are combined … in Theorem 9.48" applies 9.48
  outside its hypotheses; as948-reformulation already records that.  Per the
  filing standard, a reader would not stumble on anything new here.

## Claimed, for adversarial review
1. [D_p, D_q]1 = 4(T_p q − T_q p), and the brief's 2(p&q − q&p) is wrong.
2. Lemma A, Lemma B, and U_p x = U_{p⊥} x = U_q x = U_{q⊥} x = 0, from REC 119 +
   separation + S1.
3. i[p, q] ∈ W½(p) ∩ W½(q), so corner data cannot decide M.
4. asrt_p asrt_q asrt_p = asrt_{p&(q&p)}.  Check that REC's †-positivity is
   f†∘f for pure f and that the uniqueness clause applies to non-sharp predicates.

## Review (2026-09-26)

Break-it review vs short.tex, Reconstruction.lean, review-rec104, ERRATA; numpy M_4.

**Claim 1 ([D_p,D_q]1 = 4(T_p q − T_q p)): STANDS.**  D_r = 2T_r − 1, so
[D_p,D_q] = 4[T_p,T_q], and [T_p,T_q]1 = T_p q − T_q p since T_r 1 = r.  The
print itself says "[T_p,T_q]1 = 0 is easily seen to be equivalent to
[D_p,D_q]1 = 0" (short.tex:2233).  Numerics: residual 1e-15; the brief's
2(p&q − q&p) is off by 0.96.  (S) = ½(pq+qp) in B(H): residual 4e-9.

**Claim 2 (Lemmas A, B, four corners): statements STAND; proof of Lemma A BROKEN
as written, repairable.**
* Lemma A applies REC 119 to ω' := asrt_{p⊥} ∘ ω.  That is a **substate**, not a
  state: REC 119 and `WeteringStateOrderLemma` quantify over `Stat A` = total maps
  (short.tex:436; review-rec104) — the same defect as REC 120's ERRATA entry.
* Repair (same as REC 120's): for any state σ of {A|p⊥}, π_{p⊥}∘σ is total and
  p∘π_{p⊥}∘σ = 0, so REC 119 gives (q&p)∘π_{p⊥}∘σ = (q⊥&p)∘π_{p⊥}∘σ.  Separation
  by states *on {A|p⊥}* gives (q&p)∘π_{p⊥} = (q⊥&p)∘π_{p⊥}; precompose with the
  filter ξ_{p⊥}, using asrt_{p⊥} = π_{p⊥}∘ξ_{p⊥} (`rec109`).  (If {A|p⊥} has no
  states, id = 0 there and the identity is trivial.)  So the note's "`comp_asrtS_of`
  is not even needed" is wrong in spirit: the comprehension factorisation is
  needed, and "separation" must be on {A|p⊥}, not on A.
* Lemma B: algebra re-derived (q&p⊥ = q − q&p, q⊥&p⊥ = q⊥ − q⊥&p by S1 and
  a&1 = a); correct.  Corners U_p x = U_{p⊥} x = 0 re-derived; p⊥&p = 0 for sharp
  p is available.  Swap p↔q: fine.  Numerics: Lemma A 8e-9, Lemma B 1e-8.

**Claim 3 (i[p,q] in all four Peirce-½ spaces; corner data can't decide M):
the fact STANDS; the conclusion drawn from it is OVERCLAIMED.**
* ‖i[p,q]‖ = 0.72, all four compressions ≤ 1.4e-8.  So the corner equations
  alone do not fix R_p x.
* But that does not show "not derivable from anything REC states" (§3, verdict).
  REC 119 holds for *every* predicate a and every state with a∘ω = 0; such ω
  need not lie in a corner of p (take a = (im ω)⊥, or sharp a built from p, q:
  ⌈p&q⌉, p∧q, …).  The note tried only a ∈ {p, p⊥, q, q⊥} with corner states,
  and REC 120 (all D_p order derivations, jointly) was not exploited beyond that.
  Correct wording: "we could not derive M; corner data provably cannot".
* "Gap in the printed proof" is nonetheless **justified**, on other grounds: the
  print's only argument for [D_p,D_q]1 = 0 is "combined … in Theorem 9.48"
  (short.tex:2233), a theorem whose hypotheses (A = V* in spectral duality) are
  never established for V_A, and in a section that itself says A–S results
  phrased with real states must be reworked (short.tex:2153, 2172).  That is a
  gap whether or not M is derivable.  Keep verdict (c) open; drop "not derivable
  from anything REC states".

**Claim 4 (asrt_p asrt_q asrt_p = asrt_{p&(q&p)}): STANDS, one step unstated.**
* †-positive means f = g∘g† (short.tex:1396); uniqueness is asserted for *every*
  predicate, sharp or not (REC 100, short.tex:1857), so it applies.
* With g = asrt_p∘asrt_q, g∘g† = asrt_p asrt_q² asrt_p.  This equals asrt_p asrt_q
  asrt_p only because q is sharp: asrt_q² = asrt_{q&q} = asrt_q (short.tex:1937).
  The note skips this; for non-sharp q the claim is false as stated.
* 1∘(…) = p&(q&p) (palindrome).  B(H): √(pqpqp) = pqp; numerics 9e-9.

**Claim 5 / errata: an entry IS warranted (disagree with the note's §4).**
papers/ERRATA.md has no REC 121 entry; 9.48 appears only as a named hypothesis
in the REC 104 entry.  A careful reader checking 9.48 stumbles: the step that
carries the Jordan content has no argument in the paper's setting, and the
well-definedness line claims "commutativity of the T_{p_i} and T_{q_j}", false
already in M_2 (as948-reformulation).  Proposed entry:

> ### REC 121 — proof is a sketch; key step cited outside its hypotheses
> The proof obtains [D_p,D_q]1 = 0 (the symmetry p*q = q*p) by citing A–S
> *Geometry* Thm 9.48, which assumes V_A = V* in spectral duality with a base
> norm space; the paper does not establish this, and §5.3 itself notes that
> A–S results about real states must be reworked for internal states.  The
> components of the symmetry in the Peirce-1 and Peirce-0 spaces of p and q
> follow from Lemma 119 (via comprehensions, as in the REC 120 repair); the
> Peirce-½ component is not derived.  "Commutativity of the T_{p_i}" should
> read "symmetry p_i*q_j = q_j*p_i".  Status: statement not refuted; carried
> in Lean as the named hypothesis `AlfsenShultzJordanFromDerivations`.
> Review: `lean/docs/research/as948-discharge.md`.
