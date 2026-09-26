# Break-it review: REC §6 (Monoidal.lean, REC 122–136)

Reviewer brief: attack the named hypotheses, `rec136`'s statement, the two §6 ERRATA
entries, and the REC 128/135 grades.  Read-only; nothing compiled.  2026-09-26.

## 1. Named hypotheses

**`HancheOlsenStormerDecomposition`** (Monoidal.lean:390–407): STANDS.
- `c² = c` and `c(xy) = x(cy)` is exactly "central idempotent" (operator-commutes with
  all of `V`).
- φ-clause: the JW part `(1-c)V` embeds injectively and normally into some `M_sa`, `M` a
  vN algebra; compose with `x ↦ (1-c)x` (a normal Jordan hom, because `1-c` is
  central). The kernel is `{x ; (1-c)x = 0} = {x ; cx = x}`. `IsJordanHomInto`
  (Algebras.lean:308) does not require a unital hom, so the degenerate `c = 1`
  case is met by `φ = 0` into any vN algebra. A Type-v target exists: `B(H)` with
  `H : Type v`, which has the thesis-A instance used in `isJW_of_subsingleton`
  (Monoidal.lean:2798). Normality in all of `𝔄`, not only in `𝔄_sa`, is harmless
  because upper bounds of self-adjoint elements are self-adjoint.
- The last clause, "every Jordan hom `ψ : V → 𝔅` into a C*-algebra vanishes on `cV`", is
  **implied** by 7.2.7. Restrict `ψ` to `cV`: it is still linear, self-adjoint-valued
  and multiplicative, because `cV` is a Jordan subalgebra with the same product, and
  unitality is not required. `cV` is purely exceptional (REC 51, short.tex:923, same
  "every Jordan hom is zero" definition), so `ψ|cV = 0`. This is the literal
  definition applied to a restriction, so it is not a near-conclusion.
- Universes: the vN and C* algebras live in the universe of `V`. That is consistent with
  `IsPurelyExceptional.{v,v}` in `corner_purelyExceptional` (Monoidal.lean:2442).
- Remark: `rec135` uses the φ-clause only when `c = 0` (Monoidal.lean:2610). For `c ≠ 0`
  it derives `False` from `hvan` alone.

**`ShultzExceptionalStructure`** (Monoidal.lean:416): STANDS.
- `V ≃ₗ C(X, Alb)`, pointwise multiplicative, `X` hyperstonean. `Alb = HermMat 3 Oct`
  carries the inner-product-norm topology (Appendix2.lean:2073), which is
  finite-dimensional and therefore equivalent to the JB norm, so `C(X, Alb)` is the
  right space.
- Asking only for a multiplicative linear bijection is weaker than Shultz 1979 (also
  H-O–S 7.2.7, second half). `V = 0` gives `X = ∅`, and `rec133` handles that
  (Monoidal.lean:583).

**`AlfsenShultzFourExchangeable`** (Monoidal.lean:383): STANDS mathematically; the
citation is UNCLEAR.
- The quantifiers are right: `n ≥ 4`, nonzero orthogonal idempotents summing to `1`,
  and pairwise `∃ s, s² = 1 ∧ U_s p_i = p_j` with the correct `U_s = 2T_s² − T_{s²}`
  (`jQ`, :187). `i = j` is trivial (`s = 1`).
- Truth: by Jacobson coordinatization (n ≥ 3), the algebra is `H_n(D)` with `D`
  associative for n ≥ 4. So `V` satisfies every s-identity, including Glennie's. A
  nonzero purely exceptional ideal would map onto `H_3(𝕆)`, which fails Glennie, so
  the exceptional part of 7.2.7 is zero and `V` is JW.
- I could not check offline that A–S *Geometry* Lemma 4.4 is the right label. The
  content matches the lemma H-O–S use inside the proof of 7.2.7. If the author wants
  it, cite H-O–S Ch. 7 as a backup.

**`HancheOlsenStormerUniversalEnvelope`** (Monoidal.lean:353): STANDS and is unused.
Dropping "generates" and uniqueness only weakens it. `rec130` is proved from
`IsUniversalEnvelope` alone. Since no theorem depends on it, it cannot make anything
vacuous.

## 2. `rec136` statement (Monoidal.lean:2824): STANDS

- `JWnpcCat` (:2686) has the same Hom as `JBWnpcCat` (Reconstruction.lean:2951), namely
  `IsNPC` linear maps, and carries `jbw` plus `jw`. It is the full subcategory, as
  stated at short.tex:2407.
- The functor is `A ↦ V_A`, `f ↦ Pred(f)` (`jwFunctor`, :2717). The iso
  `Pred A ≃ [0,1]_{F A}` preserves and reflects order, preserves `ovee` as `+`, and
  sends `truth` to `1`: that is an effect-algebra iso. The `[0,1]`-action is not listed,
  but it follows from order plus sums (rationals, then monotonicity).
- "Faithful ↔ `SeparatingPredicates`" is as printed.
- Hypotheses `hirr` and `¬ScalarsAreTwo` are the print's "irreducible, ≠ {0,1}". The
  `{0}` case is handled by `trivSplit`; `[0,1]` by `rec135`.
- The existential `∃ F` is as weak as the print's "there is a functor", and the
  definition is exhibited anyway.

## 3. REC 127 false as printed (Monoidal.lean:1990): Lean STANDS; ERRATA entry: DROP

- As printed (short.tex:2329), with "Let A and B denote objects in C" (short.tex:2280),
  the statement literally includes `B = 0`. There `1_0 = 0`, so `a ⊗ 1 = 0` and `V_I ≠ 0`.
  The refutation is correct.
- Would a *reader* stumble? No.
  - It is the zero-object degenerate case: `V_0 = {0}`, and "injective into `V_{A⊗0} = 0`"
    visibly fails for trivial reasons.
  - The proof's "let ω' be any state on the second system" signals the tacit
    assumption.
  - The only use is REC 135 with `B = A_p`, `p ≠ 0`, which has states.
  - The Lean proof of REC 135 does not even use injectivity of `a ↦ a⊗1`
    (Monoidal.lean:2672–2682). It only uses the Jordan property and `1⊗1 ≠ 0`, so no
    downstream reasoning is affected.
- Under the author's standard (file only if a reader would stumble) this is a checker
  item. Keep the audit rows (`differs`); remove the REC 127 bullet from ERRATA.md:287–292.
- If kept, file the normality gap instead. At short.tex:2339, "order-isomorphism onto
  the image, hence normal" does not give sups in `V_{A⊗B}`. That gap is more
  substantive than `B = 0`, but it is also minor.

## 4. Triple product before REC 128 (short.tex:2342): STANDS; keep the ERRATA entry

Computation in an associative algebra, `x*y = ½(xy+yx)`:

- `(a*b)*c = ¼(abc + bac + cab + cba)`
- `(c*b)*a = ¼(cba + bca + acb + abc)`
- `(a*c)*b = ¼(acb + cab + bac + bca)`
- first + second − third = `½(abc + cba)`: `b` is in the middle, not the stated
  `½(acb + bca)`.

Consequences:
- With `b = a` the printed formula gives `(a*a)*c + (c*a)*a − (a*c)*a = a²*c = T_{a²}c ≠ Q_a c`.
- Swapping `a, b` changes the value, so it is not symmetric.

All three claims in the next two sentences (JW formula, `Q_{a,b} = Q_{b,a}`,
`Q_a = Q_{a,a}`) are false for the printed formula. The correct formula is
`Q_{a,b}c = (a*c)*b + (b*c)*a − (a*b)*c`, which is Lean's `jQ2 a b c` (:193, with the
arguments renamed).

A reader who checks "Note that Q_{a,b} = Q_{b,a}" against the definition stumbles at
once, and REC 128's proof relies on exactly those properties. The entry meets the
standard as a typo-class erratum. Its wording at ERRATA.md:294–298 is correct.

## 5. REC 135 repairs and REC 128 grade

- **`corner_jordan`** (:2303): correct, and useful, though "repair of a gap" slightly
  overstates it.
  - The print's `Pred(A_p) ≅ [0,1]_{V₂}` is an effect-algebra (order) iso. To make
    `V_{A_p}` purely exceptional one needs a Jordan iso.
  - A reader can get that from the known theorem that a unital order isomorphism
    between JB-algebras is a Jordan isomorphism (A–S *State spaces*; Isidro–Rodríguez).
    So it is an implicit step, not a false one.
  - The Lean route avoids that citation: `Pred(π_c)` is a Jordan hom (:2303) and is
    surjective with section `Pred(π_c†)` (:2372). Composing with it transfers pure
    exceptionality (:2442).
  - Correct. Proof grade `route` is right. Statement `ok` is right: the Lean statement
    is "V_A is JW" as printed. No ERRATA is warranted, and none was filed.
- **Bypassing `W*(V)`**: correct and needed by nothing. `IsJWAlgebra` (Algebras.lean:324)
  already provides an injective normal Jordan hom into a vN algebra, so the print's
  detour through REC 130 is redundant, not wrong. This is a simplification, not a
  repair. Grade `route` is fine.
- **`central_of_jordan`** (needed for the comprehension `π_p`): the print is silent
  there, and filling it is legitimate.
- **REC 128** (`rec128`, :2119): proved only for `a = αe+βe⊥`, `b = γf+δf⊥`, on product
  vectors. The row (papers-rec.csv:186) is `weaker|route`, which is correct.
  - REC 134 is graded `ok`, which is correct. Every symmetry has the form `e − e⊥`
    (`symmetry_repr`, :2172), so the two-block case covers REC 134's arbitrary
    symmetries.
  - The status text "ok for two-block combinations" is fine.

## Summary of recommendations

1. Drop the REC 127 ERRATA bullet (a checker item). Keep the audit rows.
   Optionally mention the normality gap in the audit note, which already does so.
2. Keep the triple-product ERRATA bullet as is.
3. Add "(label unverified; content = the n ≥ 4 coordinatization lemma used in
   H-O–S 7.2.7)" to the REC 132 docstring or row if the A–S label cannot be checked.
4. No grade changes.

**Correction (2026-09-26, `rec-citations.md`):** A–S *Geometry* Lemma 4.4 (p. 105) verified as the source of REC 132. REC 55 is Shultz 1979, Thm 3.9; H-O–S 7.2.7 gives only the JW ⊕ exceptional decomposition (REC 52) and has no "second half".
