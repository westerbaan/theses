# S1-acstar — sampled re-audit of `ok` rows (2026-09-04)

Files: `acstar-basic.csv`, `acstar-matrices-representation.csv`,
`acstar-positive.csv`, `acstar-towardsvn-avn-completeness.csv`.  44 rows
re-derived from `cstar.tex`/`vn.tex`/`asols.tex` and the Lean source; the
rows' own notes and status fields were not relied on.

**Counts: 44 CONFIRMED, 0 DEFECT, 0 UNSURE.**

## acstar-basic.csv

- CONFIRMED — line 17, 4VIII `IsAdjointTo`.  cstar.tex:416 `hilb-def`:
  `⟨Tx,y⟩ = ⟨x,Sy⟩` for all `x ∈ H`, `y ∈ K`, with the thesis's convention
  (linear in the second argument) matching Mathlib's.  Definition, proof=none.
- CONFIRMED — line 18, 4VIII `Adjointable`.  "In that case we call `T`
  adjointable" = `∃ S, IsAdjointTo T S`.  Definition, proof=none.
- CONFIRMED — line 27, 4XV `innerNorm`.  The exercise (cstar.tex:590) is
  stated for an arbitrary, possibly indefinite, inner product; the def is
  `√⟪x,x⟫` over `PreInnerProductSpace.Core ℂ V`, which is that setting.
- CONFIRMED — line 33, 4XV `inner_product_norm_of_definite`.  "prove that
  `‖·‖` is a norm when the inner product is definite"; the Lean iff is that
  clause, and its forward direction is `asols` parsec-40.150's own two lines
  (`‖x‖=0 ⟹ ⟨x,x⟩=0 ⟹ x=0`).
- CONFIRMED — line 37, 4XVI `operators_cstar_identity_2`.  Statement is
  4XVI.2 with `T` bounded (erratum parsec-40.160) and the adjoint a bare
  `S : H → H`, its boundedness in the conclusion.  *Closest call of the
  sample*: the printed proof (point 170) reaches `‖T‖ ≤ ‖T*‖` through
  `‖T‖² ≤ ‖T*T‖ ≤ ‖T*‖‖T‖` with a `T ≠ 0` split, while
  `norm_le_of_isAdjointTo` bounds `‖T*(Tx)‖ ≤ ‖T*‖‖Tx‖` and cancels
  pointwise.  Same Cauchy–Schwarz estimate on `⟨x,T*Tx⟩`, one bound taken a
  step earlier; `faithful` is not wrong, though `mild` would also have been
  defensible.
- CONFIRMED — line 54, 5IX `riesz_representation_theorem`.  cstar.tex:811
  verbatim (`∃!x, ⟪x,·⟫ = f`); the proof is `InnerProductSpace.toDual`, i.e.
  class 5, and the thesis's ker-projection construction is not transcribed.
- CONFIRMED — line 67, 7III `cstar_involution_basic_9`.  `asols`
  parsec-70.30(9) is "Combine point 3 and point 7"; the Lean proof is point 7
  at `a` and at `a*` plus point 3, nothing else.
- CONFIRMED — line 69, 7III `cstar_involution_basic_11`.  parsec-70.30(11)
  verbatim: the `a = 0` case, then `‖a‖² = ‖a*a‖ ≤ ‖a*‖‖a‖`, then the same
  applied to `a*`.
- CONFIRMED — line 107, 11VI `spectrum_bounded_3`.  `asols` parsec-110.60(3)
  verbatim: `ε := ‖(-b)⁻¹‖⁻¹`, `y = (y-b) - (-b)`, part 2.  The extra
  `Subsingleton` branch is what `Units.norm_pos` needs, not a route change.
- CONFIRMED — line 118, 11XX `spectrum_matrix`.  `spectrum ℂ A = {z | ∃ v ≠ 0,
  Av = zv}` is the exercise's clause.  `Matrix.isUnit_iff_isUnit_det` composed
  with `Matrix.exists_mulVec_eq_zero_iff` is exactly the solution's opening
  "a square matrix is invertible iff its kernel is {0}"; the local `key` is
  its "in that case `Av = λv`, and conversely".
- CONFIRMED — line 120, 11XXI `spectrum_basic_1'`,
  `spectrum_basic_1'_not_isSelfAdjoint`.  Both halves of the counterexample
  are present, and the computation is parsec-110.210(1)'s own characteristic
  polynomial `det((0 2;0 0) − λ) = λ²`.

## acstar-matrices-representation.csv

- CONFIRMED — line 4, 32I `moduleAdjointTo_unique`.  cstar.tex:5088's embedded
  "adjoint to exactly one `S`"; linearity/module-map is the sibling
  `moduleAdjointable_linear`.  "It is not difficult to see" — proof=none.
- CONFIRMED — line 17, 32IV `PaschkeJ`.  The type carrying `J = {f : f 0 = 0}`
  so that the exercise's Hilbert-module and non-adjointability clauses can be
  stated of a type; those clauses have their own declarations.  Definition.
- CONFIRMED — line 37, 32XV `bax_inner_nonneg`.  Easy half of 32XV.2, and the
  solution's own step; it factors `T = R*R` where the solution writes
  `T = (T^{1/2})*T^{1/2}` — the same one-line argument with a different
  witness.  Stated for all `x` rather than `(X)≤1`, which the solution itself
  does ("for all `x ∈ X`, and thus all `x ∈ (X)≤1` too").
- CONFIRMED — line 62, 34II `n_pos`.  All three clauses of cstar.tex:5519 as a
  TFAE, in the thesis's own shapes.  The cycle 1→3→2→1 is the printed proof:
  `C = A*A` decomposed into rows (2→1), and `B ≥ 0 iff ⟨b,Bb⟩ ≥ 0` (3→2).
- CONFIRMED — line 77, 34IX `cp_commutative_cod`.  The ℬ-commutative half; the
  proof is 34X's computation `ω(∑ bᵢ*f(aᵢ*aⱼ)bⱼ) = ω(f(c*c))` with
  `c = ∑ ω(bᵢ)aᵢ`, for every character.
- CONFIRMED — line 78, 34IX `cp_commutative_dom`.  The 𝒜-commutative half.
  34XI reduces by `ccstar-pos-mat` to `A = aB` and then uses that
  `(M_N f)(aB) = f(a)B` is positive; the Lean renders the reduction as
  "closed set containing the generators", with `ccstar_pos_mat` (whose
  printed form is already `∑ₖ aₖBₖ`) supplying the density.
- CONFIRMED — line 79, 34XII `cstar_positive_2x2matrix`.  Both inequalities of
  cstar.tex:5704; the closing "in particular" is the sibling
  `cstar_positive_2x2matrix_eq_zero`.  Proof is 34XIII: Cauchy–Schwarz for
  `⟨x,Ay⟩` at the two standard basis vectors.
- CONFIRMED — line 103, 27IV `gelfand_representation_basic_2`.  Part 2 ("γ is
  miu"); the involution clause is the theorem, the rest is carried by the
  `AlgHom` structure of `gelfandTransform`.  Class 5.
- CONFIRMED — line 131, 28II `functional_calculus_3_j`.  28II.3's first
  clause, both halves (`j : ρ ↦ ρ(a)` lands in `spec(a)`, and is continuous),
  closed by `StarAlgebra.elemental.characterSpaceToSpectrum` and
  `continuous_characterSpaceToSpectrum`.  Class 5.
- CONFIRMED — line 143, 29IX `nonneg_of_injective_miu`.  Private, and not a
  transcription of 29IX — the Exercise is stated in full by
  `injective_miu_iso_on_image` and `..._isomorphism`, each with its own row.
  Its proof is the printed step at cstar.tex:5024 ("ϱ_Ω restricts to an
  miu-isomorphism … so it suffices to show ϱ_Ω(a) ≥ 0"), justified through
  the spectrum and 17V.3.
- CONFIRMED — line 147, 30IV `omega_norm_basic_2`.  `‖ab‖_ω ≤ ‖a‖‖b‖_ω` in
  the corrected form of erratum parsec-300.40; the four counterexamples are
  the sibling row.  Closed by the operator-norm bound on Mathlib's
  `leftMulMapPreGNS` rather than transcribed, so class 5.

## acstar-positive.csv

- CONFIRMED — line 9, 13II `fpsOfCoeffs`.  Private bridge to Mathlib's
  `FormalMultilinearSeries`; 13II's own content is `radiusOfConvergence` and
  the `hadamard` theorems, each rowed.  No thesis statement, no proof to match.
- CONFIRMED — line 16, 14II `integral_norm_le`.  14II.2's closing clause; the
  bound is stated for any `M` dominating `‖f t‖` on `[0,1]`, which is
  equivalent to the sup-norm form.  The deduction from the disjoint-interval
  normal form is not transcribed (`S_𝒜` is not built), so class 5.
- CONFIRMED — line 28, 14VIII `invint_4`.  `∫_T = 2πi·wn_T(z₀)` is the
  exercise's identity rearranged.  `asols` parsec-140.80(4) reads in full
  "This is obvious if one notes that the `log` terms will cancel", and the
  Lean proof is part 3 on each side with the three logarithms telescoping and
  the three angles summing to `2π·wn` by the definition at cstar.tex:2155.
- CONFIRMED — line 53, 23VII `thesisSqrt_exists`.  Existence half for
  `ThesisPos`; uniqueness is `sqrt_existsUnique`.  `asols` parsec-230.70 is
  "This all follows without much effort from parsec-230.20", and the Lean
  proof is exactly that reduction (scale to `‖y‖ = 1`, apply the 23II
  iteration to `1 − y`, scale back by `√‖x‖`).
- CONFIRMED — line 59, 25I `thesisPos_iff_nonneg`.  25I's clauses 1 and 4;
  Mathlib's `0 ≤` is clause 4 closed under sums.  Both halves are the printed
  solution's two sentences — `c = √a` forward, `c*c ≥ 0` (parsec-240.40)
  backward, with the sum-closure the cone's definition forces.
- CONFIRMED — line 81, 20II `norm_map_le_two_mul`.  Private unital
  specialisation of 20II.2; 20II.2 itself is `weak_russo_dye_2`, whose proof
  is the printed one at cstar.tex:2894.
- CONFIRMED — line 95, 20aII `cstarEqualiser`.  cstar.tex:3059's `ℰ` as a
  ∗-subalgebra; closedness is `cstar_equaliser_1` and the instance, the
  universal property `cstar_equaliser_2_miu`/`_pu`, each rowed.  Definition.
- CONFIRMED — line 110, 22III `order_ideal_basic_1`.  `asols` parsec-220.30(1)
  step for step: `x ∈ J` with `ω(x) ≠ 0`, scale to `ω(x) = 1`, `1 − x ∈ ker ω
  ⊆ J`, so `1 ∈ J`.
- CONFIRMED — line 123, 22VIII `states_order_separating_2`.  The exercise's
  "Conclude that the set of states is order separating"; the Lean derives it
  from part 1 via 21VII `order_separating_norm` (3)→(1), with `‖ω(a)‖ ≤ ‖a‖`
  from 20II.1.  *Second-closest call*: `asols` parsec-220.80 stops after part
  1, so the only printed guidance for this clause is the word "Conclude"; the
  tree follows the derivation that word points at, so `faithful` stands, but
  `none` would not have been unreasonable.
- CONFIRMED — line 145, 24II `cstar_pos_neg_part_2`.  All five clauses of
  24II.2 (`a₊,a₋ ≥ 0`, `a = a₊ − a₋`, `a₊a₋ = a₋a₊ = 0`), closed by the CFC
  lemmas; the solution's `4a₊a₋ = |a|² − a² = 0` is not transcribed, so
  class 5.
- CONFIRMED — line 169, 26II `isLUB_zero_posPart`.  Private consequence of
  26II.3 at `a = 0`, obtained from `commutative_cstar_basic_3` (the hint's
  `½(a+b+|a−b|)` supremum), which carries 26II.3 itself.

## acstar-towardsvn-avn-completeness.csv

- CONFIRMED — line 4, 36I `SelfDual`.  cstar.tex:6123 clause for clause: every
  bounded module map `r : X → 𝒜` is `⟪y,·⟫` for some `y`.  Definition.
- CONFIRMED — line 14, 4XV `inner_polarization`.  Private auxiliary
  expressing `⟪y,Sx⟫` through four diagonal values; it is not 4XV.4, which is
  `inner_product_basic_4` in `Basic.lean` with its own row.
- CONFIRMED — line 24, 37IX `inner_self_im_eq_zero`.  Private auxiliary
  (`Im⟪x,Sx⟫ = 0` for self-adjoint `S`) inside the proof of 37IX; 37IX's three
  clauses are `hilb_suprema_1/2/3`.
- CONFIRMED — line 33, 38II `vector_functional_normal`.  Example
  cstar.tex:6434; the proof is the Example's one-line justification
  ("by hilb-suprema") spelled out as 37IX parts 1, 2 and 3.
- CONFIRMED — line 67, 39IX `ketbra_smul_left`.  Private auxiliary
  (`|cx⟩⟨z| = c|x⟩⟨z|`) for the form used in 39IX.
- CONFIRMED — line 70, 39IX `bh_np`.  Statement renders `∑ₙ‖xₙ‖² = ‖ω‖` as
  `= ω 1`; for a positive functional the tree states `‖f‖ = ‖f(1)‖`
  (`russo_dye_cor_norm`, 34aVIII), so the point is not short in the tree and
  the divergence is disclosed in the row.  The proof is cstar.tex:6697 step
  for step — 36V for `ϱ`, positivity by 25V, an orthonormal basis, 39VI.3 for
  `ω(1) = ∑‖√ϱ e‖²`, 38IV.2 for `ω'`, countable support to reindex by ℕ, and
  39VII to pass from the rank-one operators to all of B(H).  The printed
  polarisation step is not run because `hkey` proves the printed diagonal
  identity for all `u, v` at once (Parseval applied to `⟪Rv,Ru⟫`), which the
  printed computation supports verbatim.
- CONFIRMED — line 99, 74I `proto_kaplansky`.  vn.tex:4224.  The hypothesis
  `b : ℝ` where the point says `b ∈ [0,∞)` is *equivalent*, not weaker (a
  negative `b` forces `f = 0` beyond `n`, where `b = 0` also works).  The
  proof is the printed plan, including the generating family `e_{r,c}(t) =
  e(rt+c)` with `e(t) = t/(1+t²)`, the identity
  `e(b) − e(a) = s(b)(b−a)s(a) − e(b)(b−a)e(a)`, Stone–Weierstraß, and the
  reduction of a general `f = O(t)`.  The two renderings (constants omitted
  from `kapGens`; Stone–Weierstraß run in the real algebra, so "taking real
  parts" is empty) are documented and change nothing.
- CONFIRMED — line 102, 74IV `convex_usClosure`.  Auxiliary: the `‖·‖_ω` are
  seminorms, so the ultrastrong closure of a convex set is convex.
- CONFIRMED — line 114, 74IV `kaplansky_pos`.  Clause 2 with `‖a_α‖ ≤ ‖b‖`
  retained.  The proof is vn.tex:4386's two steps in its order: part 1's net
  clamped to `[−‖b‖,‖b‖]`, then `(·)₊` applied to it, ultrastrongly
  continuous by 74I, with `cfc (·)₊ b = b` the thesis's `b₊ = b`.
- CONFIRMED — line 118, 75II `sequence_separation_lemma`.  vn.tex:4469
  hypotheses and conclusion verbatim, and the proof is the printed one: the
  subsequence with `ω₀(bₙ) ≤ n⁻¹2⁻ⁿ`, `ω₁(bₙ^⊥) ≤ n⁻¹`; `a_{nm} = (1+d)⁻¹d`
  with `d = ∑_{k=n}^m k b_k` (reindexed to `Finset.range`); the `ω₀` estimate
  via `a_{nm} ≤ d`; the `ω₁` estimate via `(1+mt)⁻¹ ≤ (1+m)⁻¹(1+mt^⊥)`, which
  the thesis gets from Gelfand and the tree from `cfc_le_iff`; and the
  closing ceiling step.  (Note nit, not a grade fault: the row cites an
  "erratum parsec-750.30 (0 ≤ a_{nm} ≤ 1, not ≤ ½)" that exists nowhere in
  the tree or in `vn.tex`, which already prints `0 ≤ a_{nm} ≤ 1`.)
- CONFIRMED — line 128, 75VIII `usClosureSubalgebra`.  The ultrastrong closure
  of a C*-subalgebra as a ∗-subalgebra — asserted without argument inside the
  proof of 75VIII (vn.tex:4597, "because the ultrastrong closure of 𝒮 …") and
  stated nowhere in the thesis, so there is no printed proof to match and
  nothing of the point is missing from the tree.  Recorded in `ERRATA.md`
  (75IX).  Star-closedness goes through the ultraweak topology and 73VIII,
  as it must (43II.4).
