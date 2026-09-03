# S2-aproc — sampled re-audit of `ok` rows (2026-09-04)

Files: `aproc-duplicators-quantumlambda.csv`, `aproc-measurement.csv`,
`aproc-tensor.csv`.  33 rows re-derived from `proc.tex`/`vn.tex`/`asols.tex`
and the Lean source; the rows' own notes were not relied on.

**Counts: 32 CONFIRMED, 1 DEFECT, 0 UNSURE.**

## aproc-duplicators-quantumlambda.csv

- CONFIRMED — line 6, 127I `Duplicable`.  proc.tex:5860 Definition; the
  `Duplicator` fields are npsu (positive, `PreservesDirSups`, `δ 1 ≤ 1`),
  `unit ∈ effects`, and `δ(u ⊗ a) = a = δ(a ⊗ u)`.  Definition, so proof=none.
- CONFIRMED — line 25, 129II `ContinuousSpace`.  proc.tex:6194 part 3
  ("contains no atomic subsets") = `∀ S, ¬ AtomicSet μ S`.
- CONFIRMED — line 36, 130II `ae_const_of_atomic`.  proc.tex:6480's own
  reduction ("we may split `f` in its real and imaginary parts") is the proof;
  the Lean proof is that reduction to `ae_const_real_of_atomic`.
- **DEFECT** — line 47, 130V `discrete_ell_x`: **proof=faithful is wrong; it
  should be `none`.**  `cor:discrete-ell-x` (proc.tex:6531) is a Corollary with
  no proof point, and `asols.tex` has no solution for it (solutions stop at
  parsec 340); grep of proc.tex/asols.tex for the corollary's label finds only
  the statement and two later citations.  The row's note quotes a "PRINTED
  proof" (`combine 130IV with 130II`) that is not in the thesis — the row's own
  status field admits this as of 2026-08-29 but concluded "the verdict is
  unaffected", which is the error: with no printed argument there is nothing to
  be faithful to.  The tree's own doc comment on `discrete_ell_x` says "**The
  Corollary is printed with no proof at all.**"  stmt=ok is right (against the
  repaired 129II.2).
- CONFIRMED — line 68, 84bIII `ha_solution_set`.  Renders the solution-set
  condition of the 1252.20 proof (proc.tex:5262): `#K = 2^(2^(𝔠+#𝒜))` matches
  the printed `κ = 2^{2^{#ℂ+#𝒜}}`, and the ncpsu-map factors as an nmiu-map
  after some `γᵢ`.  Not a transcription of 84bIII itself (that is
  `hereditarilyAtomic_subalgebra`, own row in `avn-division-…`); ok/none is the
  file's convention for auxiliaries, and the note says so.  (The DISP is off —
  the declaration serves 125bII's proof, not 84bIII's — but that is a filing
  quibble, not a grade.)
- CONFIRMED — line 72, 121II `intersection_tensor`.  Matches proc.tex:4456
  clause for clause with `concreteTensor` = "least von Neumann subalgebra of
  `B(ℋ⊗𝒦)` containing all `A ⊗ B`".  The printed proof is the bare citation
  "See Corollary IV.5.10 of [Takesaki1]", so proof=none is right.
- CONFIRMED — line 83, 122VI `cor_linf_ff_3`.  Full and faithful as
  injectivity/surjectivity of `f ↦ ℓ^∞(f)` on hom-sets; the "whence
  coreflective" clause is carried by the sibling `linfCoreflective`
  (QuantumLambda.lean:655), which exists.  Exercise at parsec 1220, no printed
  argument and no solution.
- CONFIRMED — line 85, 123I `linf_generated`.  Part 1 ("`{x̂}` generates
  `ℓ^∞(X)`") as `wstar {single x 1} = ⊤`.  Exercise, no solution.
- CONFIRMED — line 87, 123I `linfT`.  The map `(f ⊗ g)(x,y) = f(x)g(y)` of
  part 3; part 3's claim that it *is* a tensor product is the sibling
  `linf_tensor` (own row 88).
- CONFIRMED — line 101, 124III `FreeMIU`.  A universal arrow from `𝒜` to the
  inclusion `W*_miu → W*_cpsu`: ncpsu-unit plus `∃!` nmiu-factorisation — the
  standard object-wise form of "the inclusion has a left adjoint"
  (proc.tex:4724).  Definition, proof=none.
- CONFIRMED — line 136, 121II `intersection_tensor'`.  Verbatim the same
  statement as the QuantumLambda declaration; thesis prints only the Takesaki
  citation, so proof=none.

## aproc-measurement.csv

- CONFIRMED — line 16, 94II `exists_cornerProjMap`.  Part 9 of the exercise at
  proc.tex:194 ("the projection `a ↦ eae` is an ncpu-map").
- CONFIRMED — line 25, 96III `ncp_uwlim`.  Main claim of proc.tex:363; the
  Lean proof is the printed one (`f(a)` is a limit of positive `f_α(a)`, cone
  ultraweakly closed by 44XI).
- CONFIRMED — line 34, 98I `stdCorner`.  Definition part 2 (proc.tex:551);
  the missing "p is an effect" is harmless as the note says (`floor p` agrees
  with the printed `⌊p⌋` on effects and is junk elsewhere).
- CONFIRMED — line 72, 100II `isPure_adSelf`.  Part 3 of the exercise at
  proc.tex:931; `adSelf a` is `a*(·)a` by `adSelf_apply`.
- CONFIRMED — line 86, 101VI `Contraposed`.  The third of the point's three
  equivalent conditions (proc.tex:1091), `⌈f(s)⌉ ≤ t^⊥ ⟺ ⌈g(t)⌉ ≤ s^⊥`, with
  `diamondUp f s = ceil (f s)`; the equivalence with the other two is
  `contraposed_iff_diamond`.
- CONFIRMED — line 90, 101VII `equivalent_examples_1'`.  Part 1's third clause
  ("in particular, `π_s` and `c_s`"); the middle clause is the sibling
  `equivalent_examples_1_corners` (Measurement.lean:4528).  101VII is an
  Examples point with no proof point, so proof=none — borderline, since the
  printed "in particular" prescribes deriving it from the middle clause and
  ours proves it directly, but the vocabulary puts Example points under `none`
  and the file grades every other 101VII clause the same way.
- CONFIRMED — line 125, 104III `centrally_similar_basic_3`.  Matches the
  repaired part 3 as currently printed (proc.tex:1488: `⌈p⌉=⌈q⌉=1`, `p`,`q`
  commute, both `(p∧q)/p`, `(p∧q)/q` central), with `p ∧ q` the meet of the
  commuting pair recalled from 26II.6 in the exercise's own preamble.
- CONFIRMED — line 126, 104III `centrally_similar_basic_4_counterexample`.  A
  counterexample record, ok/none as everywhere in this family.  Note the note
  is loose: "as printed" means *pre-erratum* — the current proc.tex part 4
  carries `⌈p⌉=⌈q⌉=1` (added at b154f62, erratum `parsec-1040.30`), which the
  witness `p=(1,0)`, `q=1` fails, and part 4 as printed today is proved at
  `centrally_similar_basic_4` (row 130).  Note imprecision, not a wrong grade.
- CONFIRMED — line 137, 104VII `ceil_mul_proj_mul_of_comm`.  Step 1 of the
  proof at proc.tex:1562, extracted; proof=none avoids double-counting, since
  steps 1–2 are graded `faithful` on the sibling row 138
  (`positive_quotients_step12`).
- CONFIRMED — line 148, 105IV `isDiamondSelfAdjoint_cornerMap`.  Part 1 with
  the corner index as a parameter (private auxiliary for part 3).
- CONFIRMED — line 149, 105IV `chevron_f_purely_positive_1`.  Part 1
  (proc.tex:1748): `⟨f⟩` on `⌈f(1)⌉𝒜⌈f(1)⌉` via the chevron formula
  `⟨f⟩ = π_{⌈f(1)⌉} ∘ f ∘ c_{⌈f⌉}` of 105IV.1/105III.  Exercise, no solution.

## aproc-tensor.csv

- CONFIRMED — line 34, 111XII `vnTensorProduct_exists`.  The exercise
  (proc.tex:2589) prescribes "using `ngns` and `special-tensor`", and the proof
  is exactly `ngns A`, `ngns B`, `special_tensor` on the two ranges.
- CONFIRMED — line 48, 112V `basic_state_inner_product`.  Conjugate symmetry
  plus positivity; definiteness is not claimed and cannot be — 112II itself
  calls `‖·‖_ω` a *semi*-norm.  The exercise's hint (`product-state-positive`)
  is what the positivity half uses.
- CONFIRMED — line 53, 112VIII `tensorNorm_nonneg`.  One of the four norm
  axioms of the exercise at proc.tex:2855; siblings (rows 54–57) carry the
  rest, `tensor_product_norm` assembles them.  Exercise, no solution.
- CONFIRMED — line 58, 112IX `product_functional`.  proc.tex:2860 ("show that
  `f ⊙ g` is bounded and ultraweakly continuous for `f ∈ 𝒜_*`, `g ∈ ℬ_*`,
  perhaps using `luws`"); the proof takes the hint.  The unused boundedness
  hypotheses are recorded in the doc comment, as the note says.
- CONFIRMED — line 65, 112X `tensor_basic_1_unique`.  Part 1's third claim
  ("every basic functional is of this form for some **unique** `ω ∈ Ω`") as an
  `∃!`.  Exercise, no printed argument for that clause.
- CONFIRMED — line 82, 114I `tensor_universal_property_extra`.  All five
  clauses of proc.tex:3059; `β_γ` as an arbitrary ultraweakly continuous `g`
  with `g ∘ γ = β` is the same map by 112XI's uniqueness.
- CONFIRMED — line 100, 115V `GenAlg`.  Private auxiliary: the thesis's `𝒯`
  (proc.tex:3296) as an algebra in its own right.
- CONFIRMED — line 104, 116I `exists_predualTensor`.  Well-definedness of
  `f ⊗ g`, which the Lemma (proc.tex:3409, `‖f⊗g‖=‖f‖‖g‖`) presupposes; the
  Lemma itself is the sibling `product_functional_norm` (row 105).
- CONFIRMED — line 118, 116III `continuous_ultraweak_vtmul_right`.  The
  normality half of part 5 (`a ⊗ (·)` is an ncp-map); the full part 5 is row
  120, which carries its own `weaker` verdict.
- CONFIRMED — line 129, 117III `sumTmul`.  The bilinear map of the Proposition
  at proc.tex:3764 (printed `(a_i ⊗ b)_i`, plainly `(a ⊗ b_i)_i`); the
  Proposition itself is `tensor_distributes_over_sums` (row 130).
- CONFIRMED — line 131, 118II `ceil_tensor`.  Part 1 (proc.tex:3808); the
  proof is the printed one step for step — `ncp_ceil` (60VI) on `(·) ⊗ b`, then
  on `⌈a⌉ ⊗ (·)`, then `⌈a⌉ ⊗ ⌈b⌉` is already a projection.
