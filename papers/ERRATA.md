# Errata in the follow-up papers

One section per paper (tag as in `lean/Papers/README.md`); one entry per point, citing the point number, the print, the problem, the repair and the Lean witness.

## OAP — *A characterisation of ordered abstract probabilities* (arXiv:1912.10040, `1912.10040/first.tex`)

* **OAP 2** (`ex:orthomodularlattice`, first.tex:390, Example) — **false as printed.**
  The print makes an orthomodular lattice an effect algebra with
  `x ⊥ y ⟺ x ∧ y = 0`.  Complements are then not unique: in `MO2` the atoms
  `a`, `b` have `a ∧ b = 0` and `a ∨ b = 1`, yet `b ≠ a^⊥`.  Repair:
  `x ⊥ y ⟺ x ≤ y^⊥` (the two agree in a Boolean algebra, which is the only
  case the paper uses, Example 6).  Lean: `Papers.OAP.oap2_false_as_printed`
  (refutation), `Papers.OAP.oap2_le_iff` (repaired claim).
* **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), third clause —
  **false as printed.**  For `S ⊆ [x,1]` the print reads
  "`⋀_{s∈S} s ⊖ x` exists ⟹ `(⋁S) ⊖ x = ⋁_{s∈S} s ⊖ x`"; the premise must be
  `⋁_{s∈S} s ⊖ x` (a supremum).  As printed it fails already for `x = 0`: in
  the Wright triangle `{a₁, a₂}` has infimum `0` but no supremum.  Lean:
  `Papers.OAP.oap24_3_false_as_printed` (refutation), `Papers.OAP.oap24_3`
  (corrected clause).
* **OAP 22** (`lem:forcing`, first.tex:727, Lemma), proof, first line — typo:
  "Since `a ≤ a'` and `b ≤ b'`" should read "Since `a ≤ b` and `a' ≤ b'`".
  Statement unaffected (`Papers.OAP.oap22_forcing`).
