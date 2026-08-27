# Statement & proof audit

A meticulous pass over **every** statement in the two theses that this tree
transcribes, asking two questions of each:

1. **Does our Lean statement say what the thesis statement says?**
2. **Does our Lean proof follow the proof the thesis gives?**

Started 2026-08-20 at commit `f6789a3` (1759 statements carrying a **DISP**
number across 30 modules).  This audit **records** divergences; it does not
repair them.  Nothing in the tree is changed on the strength of a row here —
a repair needs its own commit, and a change to a *statement* needs an author
ruling.

## Why a fresh pass

Fourteen statements have already been found, one at a time and by accident,
to be quietly weaker than or differently shaped from their sources — 30X
dropping `ϱ_Ω`, 51IX dropping ℂ-homogeneity, 28II.4 dropping the identification
with `f(a)`, 167I dropping `[VonNeumannAlgebra]` on all six algebras, 164II.2b
strengthened into a falsehood.  Each was found while working on something
else.  This is the systematic version of that check.

## Schema

One row per thesis statement, pipe-separated, in
`docs/audit/<module-slug>.csv`:

```
DISP|lean_name|module|stmt|proof|note
```

* **`stmt`** — **is the thesis's point stated in the tree?**  Not "does this
  one declaration say all of it" — see *What `stmt` is a verdict about*
  below.
  * `ok` — faithful: same hypotheses, same conclusion, same quantifiers, same
    direction and variance.  Also the verdict when the named declaration
    renders part of the point and named **siblings** carry the rest.
  * `weaker` — ours assumes more, or concludes less, **and no declaration in
    the tree makes up the difference**.
  * `stronger` — ours assumes less, or concludes more.  (Also false-as-ours
    if the extra strength is not actually true.)
  * `differs` — neither weaker nor stronger; a different shape.
  * `unsure` — could not settle it; the note says what is in the way.
* **`proof`** — does our proof follow the thesis's?
  * `faithful` — the thesis's argument, step for step (divergence class 1).
  * `route` — a different route (class 2).
  * `mild` — the thesis's route with a local deviation (class 3).
  * `mathlib` — closed by a Mathlib lemma without transcribing the author
    (class 5).
  * `none` — the thesis gives no proof (Definition, Example, or a bare
    citation), so there is nothing to match.
  * `sorry` — not proved here.
  * `unsure`.
* **`note`** — free text, **required** whenever `stmt` is not `ok` or `proof`
  is not `faithful`/`none`.  Say precisely what differs.  Empty otherwise.

Rows are in DISP order.  A statement transcribed by several Lean declarations
gets one row per declaration.

### What `stmt` is a verdict about

**`stmt` grades the thesis point, not the declaration in isolation.**  The
count of `weaker` rows is read as "this many of the theses' points are not
fully stated in the tree", and it only means that if the class is assigned
that way.

So: a row is `weaker` **only when the point it records is not fully stated
anywhere in the tree** — not by the named declaration, not by a sibling in
the same file, not by a declaration in another module, not by the Mathlib
carrier the module builds on.  Concretely, when the named declaration renders
less than the point:

1. **Look for the rest of the point before grading.**  A clause the audit
   once found missing is very often added later beside the declaration, under
   a name the row never learned.  Grep the module for the point's other
   clauses by their *content*, not by the row's `lean_name`.
2. **If a sibling carries the rest, the row is `ok`.**  Extend `lean_name` to
   name every declaration that carries a clause, comma-separated, and say in
   the note **which declaration carries which clause**.  A reader must be
   able to get from the row to the whole point without re-deriving the search.
3. **If a separate row already exists for the sibling**, leave `lean_name`
   alone — the duplicate name buys nothing — and name that row in the note
   instead.  The row is still `ok`.
4. **If some clause is genuinely nowhere**, the row stays `weaker`, the note
   names *exactly* the missing clause, and — this is the part that keeps
   going wrong — the note also names the siblings that do carry the other
   clauses, so the next pass does not re-discover them.
5. A row may stay `weaker` while its declaration is the tree's *best* form of
   the point: adding a hypothesis the printed statement lacks is "assumes
   more" even when the printed statement is false without it.  Those rows
   carry an `ERRATA.md` row or an author ruling, and the note says which.

**What must never survive is a `weaker` row whose own note says the point is
fully covered.**  If the note ends "…now stated in full as `foo_bar`", the
class is wrong, not the note.  Between 2026-08-21 and 2026-08-26 four repair
waves left 39 such rows behind — the repair was made, the sibling was named
in the note, and the class was left at `weaker` "for the named declaration".
That made the `weaker` count 85 where the honest figure was 46, and nobody
could tell from the number which rows were real.

The same rule decides `lean_name`: it is the list of declarations that
together carry the point, so **`scripts/audit_check.py`'s phantom check reads
every comma-separated name in it**.  A `lean_name` that is prose rather than
a name list (`Mathlib EuclideanSpace ℂ (Fin N) (no declaration; …)`, used
where the carrier is Mathlib's and the tree only documents it) is skipped by
that check, so use it only when there really is no declaration to name.

## Locating a statement in the sources

**Line references drift** — every doc comment carries one (`dils.tex:5024`)
and they are a starting point only.  Locate by point number instead.  A DISP
number `NxR` decodes as:

* `N` — the parsec: `\begin{parsec}{N0}`, e.g. `164` ↦ `{1640}`.
* `x` — an optional lowercase letter for a *sub*-parsec: `a` ↦ `{N1}`,
  `b` ↦ `{N2}`, …  So `125d` ↦ `\begin{parsec}{1254}` and `84b` ↦ `{842}`.
* `R` — a roman numeral giving the point *inside* that parsec:
  `\begin{point}{R0}`, e.g. `II` ↦ `{20}`, `XI` ↦ `{110}`.
* A trailing `.k` or `.2b` names a numbered clause within the point.

The proof, where there is one, is normally the *next* point (`Proof`), or the
following few.

## Roll-up — **complete**

All 30 modules audited, 2026-08-20.  Rows exceed the 1759 DISP-carrying
`theorem`s because auditors also covered DISP-carrying definitions,
structures and private auxiliaries.

| fragment | rows | stmt not `ok` | proof not `faithful`/`none` |
|---|---:|---:|---:|
| `acstar-basic` | 109 | **16** (5 stronger, 11 weaker) | 72 |
| `acstar-matrices-representation` | 118 | **28** (1 stronger, 27 weaker) | 56 |
| `acstar-positive` | 157 | **9** (1 stronger, 8 weaker) | 66 |
| `acstar-towardsvn-avn-completeness` | 144 | **8** (1 stronger, 7 weaker) | 21 |
| `aproc-duplicators-quantumlambda` | 123 | **19** (10 differs, 2 stronger, 7 weaker) | 49 |
| `aproc-measurement` | 153 | **9** (1 differs, 8 weaker) | 13 |
| `aproc-tensor` | 148 | **8** (1 stronger, 7 weaker) | 19 |
| `avn-basic` | 137 | **12** (1 stronger, 11 weaker) | 19 |
| `avn-division-normalfunctionals` | 210 | **9** (1 stronger, 8 weaker) | 13 |
| `avn-projections` | 165 | **13** (2 differs, 4 stronger, 7 weaker) | 30 |
| `bdils-hilbertmodules-selfdualcompletion` | 125 | **14** (5 stronger, 9 weaker) | 32 |
| `bdils-paschke-stinespring` | 70 | **18** (1 differs, 12 stronger, 5 weaker) | 21 |
| `bdils-pure-beff-states-effectalgebras` | 224 | **37** (3 differs, 12 stronger, 22 weaker) | 36 |
| `bdils-selfdual-kaplansky` | 98 | **19** (2 differs, 2 stronger, 15 weaker) | 34 |
| `beff-dagger-diamondamp` | 117 | **11** (1 stronger, 10 weaker) | 13 |
| `beff-effectus-quotients` | 94 | **6** (6 weaker) | 15 |
| `beff-vnexamples` | 56 | **17** (11 differs, 6 weaker) | 11 |
| **total** | **2248** | **253** | **520** |

**253 of 2248 statements do not match their source** — 174 `weaker`, 49
`stronger`, 30 `differs`, **0 `unsure`**.  On the proof side, 753 are
`faithful` and 975 have no thesis proof to match (`none`); 520 diverge — 247 a
different route, 141 mild, 114 closed by Mathlib, 18 `sorry`.

*(That is the 2026-08-20 snapshot and is kept as one.  Live counts, 2026-08-27
after the `stronger`/`differs` sweep: **2475 rows, 66 `weaker`, 50 `stronger`,
38 `differs`, 2321 `ok`**.  Earlier that day the figures were 2336 rows, 46
`weaker`, 57 `stronger`, 39 `differs` — rows have been added since by the
coverage and 42I/49II passes, so read a count only with its date.  The `weaker`
figure had fallen from 85 to 46 in the stmt-class pass of 2026-08-27, which did
not repair anything: 39 of the 85 named points that four earlier repair waves
had **already** put in the tree, under sibling declarations, and had left
classed `weaker` anyway.  See *What `stmt` is a verdict about* above for the
rule that keeps this from recurring.

The `stronger`/`differs` sweep of the same day moved ten rows: three
`stronger → differs` (169XII, 169XI.1, 153I — mixed direction), three
`stronger → weaker` (169XI.2a, 169XI.2b, 153IV — the reason for `stronger` had
expired and nothing was left pulling that way), and four to `ok` (164IX,
158V.3, 158V.4, and three of the four 49II `differs` rows, whose point is stated
on the type by the sibling `bah_vn`).)*

### Standing observations

* **A missing statement can orphan a proved one — and closing it un-orphans
  the other.**  36II ("every Hilbert space is self-dual") had no declaration,
  so `exists_rho` (39IX) and `bh_bounded_uw_complete` (76III) went straight to
  Mathlib's Riesz instead of instantiating 36V at `𝒜 = ℂ`, leaving **36V**
  proved in full and used by nothing.  *Closed 2026-08-27*: 36II is
  `selfDual_hilbert` (`TowardsVN.lean:278`), with four consumers, and 36V
  `chilb_form_representation` now has five — `exists_rho` takes the thesis's
  own route through 36II and 36V (`TowardsVN.lean:2019`).  The observation is
  kept because the mechanism is general and the tree took months to notice
  this instance of it: the audit records what each declaration says, and a
  point nobody stated has no row to be wrong.

* **A stale "still `sorry`" has now driven two live divergences.**
  `A/Proc/Duplicators`' 129X takes an arbitrary np-functional instead of the
  thesis's integral state, and the *stated reason* is that `Linfty-vn` (51IX)
  "is still `sorry` in the tree" — `A/VN/Basic` has contained no `sorry` for a
  long time.  Together with the three in `A/Proc/Measurement`, that is four
  proof routes resting on an obsolete premise.  Several file headers still
  read "Statements only; every proof is `sorry`" on files with none.
* **A repaired definition can orphan the thesis's own lemma.**  129II.2's
  `DiscreteSpace` is *partitioned* by atoms on an author ruling (QUESTIONS
  **A6**), not "covered" as printed — under the printed form 130V is false,
  129VI vacuous and 127III's proof gapped.  But the printed proof of 129VI
  does not survive the repair either, so it is replaced by Zorn on disjoint
  families — which leaves the thesis's own choice-free 129IV `measure_zorn`
  proved but unused by its intended consumer.

* **Structures are not uniformly bad — check, don't assume.**  Five in
  `B/Dils/{HilbertModules, SelfDualCompletion}` were compared field by field
  and are **clean**: `BInner` (141II), `IsBSesquilinear` (142VII), `IsONBasis`
  (149I), `SelfDualCompletion` (150II) and `IsCompatExt` (150XI).  Where a
  point's clause is not a field it is *proved* nearby (definiteness, the
  seminorm identifications), rather than lost as in 164II `ExtTensor`.
* **"Uniformly continuous" reduced to "preserves limits".**  148III asserts
  the three module operations are *uniformly* continuous — which is what 150IX
  then uses to extend them to `V̄`.  All three of our declarations state only
  preservation of ultranorm limits.  For addition the real content is in the
  tree untagged; for `x ↦ [x₀,x]` and `b ↦ x₀·b` it is nowhere.

* **Hypotheses that the proof never uses are a reliable smell.**  90II.1
  assumes both compared elements self-adjoint where the point says *order
  separating* for arbitrary `a` — and the two hypotheses are used **nowhere**,
  the proof going straight to a lemma that takes an arbitrary element.  The
  statement is therefore weaker than what we already prove.  (Contrast
  `pseudoinverse_basic_2'_4`, where the unused `hcomm` **is** what the author's
  ruling asked for: the erratum compressed the conclusion, not the
  hypotheses.  An unused binder is a question to ask, not a defect by itself.)
* **`∃!` can be vacuous.**  81VIII.2 writes `∃! c, (three properties) ∧
  UWTendsto … c` — but an ultraweak limit is already unique, so the `∃!` is
  automatic and uniqueness *among the three properties* is not delivered,
  which is what the thesis asserts.

* **A statement can be missing from the tree and still be *used*.**  24II
  part 4 (`‖a‖ = ‖a₊‖ ∨ ‖a₋‖`, added by addendum `parsec-240.20`) is stated
  nowhere — yet `A/CStar/Matrices.lean:754` reaches it through Mathlib's
  `IsSelfAdjoint.norm_eq_max_norm_posPart_negPart` to supply our 32XV.3 repair.
  Grepping for a statement's *name* will not find these; only reading the point
  will.
* **Editing a point can orphan its solution.**  `cstar.tex` 26II gained a
  fifth item 22 hours ago, but `asols.tex`'s `parsec-260.20` still has five
  items whose fifth proves the *old* claim `|a+b| ≤ |a|+|b|` in the
  commutative case — something the exercise no longer asks.  So the new item 5
  has no solution and the solution's item 5 answers nothing in the exercise.

* **"Still `sorry`" claims in doc comments go stale and cost proofs.**
  `A/Proc/Measurement` carries four that are now false — the module header on
  `exists_sqBracket`/`exists_diamondDown`, and three naming 63IV, 81VI/VII/IX
  and 98II as open when all are proved.  **Three of them are the stated reason
  for a proof-route divergence that is no longer forced.**  A stale
  "still `sorry`" is not cosmetic: it is a live instruction to take the long
  way round.
* **A displayed axiom can be mistyped without asserting anything false.**
  106III.1's conjunct for axiom (C) *used to read* `p ∗ (q ∗ q) = (p ∗ p) ∗ q`
  where (C) is `p ∗ (p ∗ q) = (p ∗ p) ∗ q` — an inner `⌈q⌉` for `⌈p⌉`.  The two
  coincide for effects, so the theorem was true; it just was not the axiom.
  *Repaired, and re-read 2026-08-27* (`Measurement.lean:8747` is now the axiom);
  the row stays `differs` for a different reason — the point's "except (A)" is
  rendered as `¬ IsSequentialProduct` rather than as `¬(A)`.  The observation is
  kept because the shape is general.

* **An isomorphism of categories rendered as an equivalence.**  188III and
  188IV build identity-on-objects functors with two-sided inverses; our
  `par_tot_equiv`, `tot_par_equiv` and the two Cho-theorem halves assert only
  `Nonempty (… ≌ …)`.  The gap is recoverable — both functors *are*
  identity-on-objects and are proved `Full` and `Faithful` — but it is never
  stated, and it propagates into Cho's theorem.
* **"Has all X" headlines dropped in favour of the witness.**  200III ("an
  effectus with comprehension has **all** kernels") and 205II (likewise for
  cokernels) are each rendered by their second sentence only — the particular
  map that *is* a kernel — with no `HasKernels`/`HasCokernels` and, in 200III's
  case, without even assuming `[HasComprehension C]`.
* **Good news worth recording:** the partial-form machinery of `Effectus.lean`
  (`FinPAC`, `EffectusPartialForm`, `IsTotal`, `predEffectAlgebra`) was
  compared field by field with 180VII and **every clause is present**.  So
  QUESTIONS **B13**'s weakness is in `effectus_vn_partial`'s statement in
  `VNExamples`, not in the definitions it rests on.

* **A repair lands under a new name, and the row keeps the old verdict.**
  This is now the audit's most common defect, and it is invisible from the
  class column alone.  Four repair waves between 2026-08-21 and 2026-08-26
  added the missing clause *beside* the flagged declaration — `vn_equalisers`
  got `vn_equalisers_miu`/`_cpsu`, 48V's `varrho_Omega_normal` got
  `gnsRepFam_normal`, 161II's `hilbmod_el2` got the whole `L2` module — wrote
  the sibling into the row's *note*, and then left the class at `weaker`
  "for the named declaration".  39 rows were in that state on 2026-08-27, 46%
  of the `weaker` count.  Two passes differed on the convention, which is why
  it went unnoticed: the B/Eff pass extended `lean_name`, the A/VN passes
  named the sibling only in prose.  The rule is now written down under
  *What `stmt` is a verdict about*.

* **A negative grep has a short shelf life, and it is not evidence a later
  pass can inherit.**  Two rows added by the coverage pass of 2026-08-27
  (3VII, 4IX in `acstar-basic`) each rested on a stated grep result that was
  *already false when written*: 3VII said nothing in the tree exhibits two
  non-commuting matrices (`bhTwoProj_not_commute_swap`,
  `A/Proc/Measurement:6073`, does), and 4IX said `c₀₀` is absent from the tree
  (`projection_on_c00`, `A/CStar/Basic:660`, is stated over it — 200 lines
  below the doc block the row is about).  Both verdicts survive on *narrower*
  grounds, but a reason of the form "grep finds nothing" must name the pattern
  and the scope, or the next reader cannot tell a real absence from a search
  that looked for the wrong token.

* **A check that skips a shape stops seeing that shape.**
  `scripts/audit_check.py`'s phantom check excluded any `lean_name` containing
  a space — a guard meant for prose entries like `Mathlib EuclideanSpace ℂ
  (Fin N)`, which silently exempted every row naming two or more declarations.
  46 rows were unchecked and one of them, 198II's `PredSquare.category`, was a
  phantom: the category structure it named is an anonymous `instance` with no
  name at all.  The check now reads every comma-separated name and skips only
  fields that are genuinely prose.

* **A missing field in a `structure` propagates silently.**  `B/Dils`'s
  **164II `ExtTensor`** *used to omit* the point's clause that `η` is
  *injective* (equivalently, definiteness of the inner product on `X ⊙ Y`, which
  164VI proves) — it was not a field and was stated nowhere, so
  `univprop_ext_tensor` was `weaker` in turn and `ext_tensor_uniqueness`
  `stronger`, quantifying over a wider class than the thesis does.  Nothing
  downstream looked wrong, which is the point of the observation.  *Closed, and
  re-read 2026-08-27*: `η_injective` is a field (`SelfDual.lean:6077`, in kernel
  form), `univprop_ext_tensor` is `ok`, and `ext_tensor_uniqueness` was moved
  from `stronger` to `ok` in the sweep of that day — its `stronger` grade had
  outlived the repair by four days.
  Audit `class`/`structure`/`def` field by field against the point.
* **An unformalized construction can hollow out a statement that looks fine.**
  **161II**'s right-`ℬ`-module, pre-Hilbert-module and self-duality structure
  on `ℓ²((pᵢ))` is asked for by the exercise and formalized nowhere; that is
  *why* 162IV is stated through bases, and it means its "`X ≅ ℓ²(…)`" is not
  actually available in the tree.

* **A whole closing Theorem can be missing.**  `A/VN/Projections` renders
  **70III** — *every commutative von Neumann algebra is nmiu-isomorphic to
  `⊕ᵢ L^∞(Xᵢ)`* — by its *reduction* only: an orthogonal family of np-functionals
  with central carriers joining to `1`.  54XI is never applied, no direct sum
  is formed, no nmiu-isomorphism appears.  A `FIXME` in the doc admits it.  The
  same shape recurs at 67IV.2 and 69IVa: an **isomorphism** in the source
  rendered as bare bijectivity, or as two of its consequences.
* **Stale doc comments about errata cut both ways.**  Two of this module's
  docs claim an erratum is still outstanding when `vn.tex` already carries the
  fix (`ncp_ceill` on parsec-610.20, `cceil_basic_2` on parsec-680.40).  The
  statements are right; only the prose is wrong — the mirror image of 33III,
  where the prose described a *superseded* version of the gap.

* **Our doc comments can misrecord what is missing.**  `A/CStar/Matrices`'s
  33III says only "`M_n f` need not be positive", and its doc comment explains
  the omitted clause in the *pre-erratum* form ("need not be bounded") — but
  erratum `parsec-330.30` reverses that clause, asking one to show `M_n f`
  **is** bounded by `n²‖f‖`.  So the file records the wrong thing about its own
  gap.  When a point has an erratum, audit against the corrected form and
  check that our doc comment did too.
* **Dropping a clause can cost a downstream proof.**  34XII omits the Lemma's
  final "in particular, if `p = 0` or `q = 0` then `a = a* = 0`" — which is
  exactly what the thesis uses to finish Choi, so `choi_2` substitutes a
  private `col_eq_zero` for it.  A missing clause is not always inert.
* **Mathlib classes in hypothesis position assume what the thesis proves.**
  Where a statement takes `[CStarModule …]` or `[InnerProductSpace ℂ H]`, the
  class axioms are assumed rather than established: 32VI and 4XV state
  Cauchy–Schwarz only for *definite* inner products where the source allows
  any, and 32IX.1/4III.1 reduce "defines a norm" to the defining equation.
  Bundled Mathlib *objects* appearing in the statement (`gelfandTransform`,
  `gnsStarAlgHom`) are treated as content that is present; classes in binder
  position are not.

* **Seven thesis defects now, not four.**  `B/Dils` adds three: **155II**
  (KSGNS) prints the adjointable map as `T : Y → X`, which does not typecheck
  against the thesis's own `ad_T` of 153I — Kasparov's direction, and ours, is
  `T : X → Y`; **157VI** says "pick `T ∈ ϱ(𝒜)^□`" and then forms `√T`, so its
  claim that `φ_T` is ncp is false without `0 ≤ T`; and **140X.1** prints the
  triple as `(𝒜, ϱ, id)` where the dilating algebra must be `ℬ` (`bsols.tex`
  confirms `𝒫 = ℬ`).  `B/Eff` adds a likely eighth: eff.tex **227III.4** gives
  left-modularity as `f^□(f_⋄(IM k)) = IM k ∨ ⌈1∘f⌉` where `f^□(0) = ⌈1∘f⌉ᵖ`
  and 228II's condition (1) uses `⌈1∘b⌉ᵖ`; the two points are inconsistent and
  228II is right.  227III.4 is not formalized, so nothing in the tree is wrong.
* **One of our statements is false, not merely weaker.**  **139XI**
  `ess_uniq_pur` asserts the conclusion for *arbitrary* `V, W`, dropping all
  three alternative hypotheses the current `dils.tex` carries and `berr.tex`
  says are required.  Its proof is `sorry`, so nothing false is derived — but
  the statement must not be proved as it stands.  The author is revising this
  exercise now; audited against the text at `ea8cfa2`.
* **Doc-comment DISP labels are not reliable.**  `B/Eff/VNExamples` cites
  `31IV` where the rest of the tree writes `30IV`, and names 199II/197II/202I/
  203I.1/203IV for points that are actually 199V/197IV/202IV/203III/203III;
  `B/Dils` labels `nmiu_forall_mem` **138II** when its content is **138IV**,
  and cites **154IV**/**154II** for formulas that are in **154V**.  A wrong
  label sends the next reader to the wrong point.

* **Four thesis statements are false as printed, none of them previously
  recorded.**  Three share one shape — a monotonicity or positivity clause
  stated with no positivity hypothesis: **111IV** `mult-completely-monotone`
  (`(a)≤(ã)`, `(b)≤(b̃)` ⟹ `(ab)≤(ãb̃)`; at `N=1`, `a=b=−1≤0`), **116III.1**
  (`a₁⊗b₁ ≤ a₂⊗b₂` for all `a₁≤a₂`, `b₁≤b₂`; same counterexample at
  `𝒜=ℬ=ℂ`), and **116III.5** (`a ⊗ (·)` an ncp-map for *every* `a`).  The
  fourth is **42III**, which describes the ultrastrong opens with `‖a−b‖_ω ≤ ε`
  where it must be `< ε` — with `≤` a closed ball would be open.  In every
  case our Lean statement silently carries the repair, so it is our *statement*
  that is `weaker`, not our proof that is wrong.
* **A DISP-tagged declaration is not always the right one.**  `A/VN/Basic`'s
  **48V** is rendered by a statement strictly weaker than the point (it fixes
  the family `Ω` and then ignores it) — while the thesis's actual statement
  *is* in the file, as `gnsRepFam_normal`, carrying no doc comment and hence no
  DISP at all.  Auditors should check the neighbourhood, not just the tagged
  declaration.
* **Multi-part exercises rendered by one clause** are the commonest
  divergence by far, in every module audited so far.  Check every numbered
  part, including the "and conclude that …" tails.

* **Deliberate weakenings are mostly unmarked.**  `A/CStar/Basic` carries two
  doc comments saying in so many words that only a "sample claim" of a
  multi-part exercise is stated — and a grep shows those are the *only* two
  such admissions in the whole tree.  So the other weakenings this audit finds
  will not announce themselves.
* **The commonest shape is a multi-part exercise rendered by one clause.**
  9X.1 (whole cone property → the scalar clause), 4III.1 ("the operator norm
  is a norm" → definiteness), 4XV.1–.4 (indefinite inner products →
  `InnerProductSpace`), 7III.5 (ℝ-linear → additive).  None of these is false;
  each says less than the point it cites.
* **`proof = mathlib` is the norm, not the exception**, in the elementary
  chapters: 43 of 109 rows in `A/CStar/Basic`.  That is a legitimate choice
  for facts Mathlib already has, but it means the *thesis's* argument is
  unexhibited, and in a few places it inverts the thesis's own dependency
  order (11XIII from 11XV.1, which the thesis proves from 11XIII).

## Triage

The audit is complete and nothing has been repaired.  The 253 statement
divergences and 520 proof divergences sort into six piles.

### 1. Thesis defects — for `ERRATA.md` (author's call)

Sixteen, none previously recorded.  Four are **false as printed**: **111IV**,
**116III.1**, **116III.5** (monotonicity clauses with no positivity
hypothesis) and **175II.2** (`[0,u]_G` with no `0 ≤ u`).  Two make a claim
that cannot typecheck: **155II** (KSGNS prints `T : Y → X` against its own
`ad_T`) and **192IV** (the *M*-affine parenthetical, in both composites).
The rest are wrong objects or wrong symbols: **42III** (`≤ ε` for `< ε`),
**140X.1** (`𝒜` for `ℬ`), **157VI** (`√T` for a `T` never assumed positive),
**158Ia** (`a`/`b` interchanged, net in the wrong algebra), **159VIII** (np-map
of the wrong algebra), **159IX** (`Y` never introduced), **15I** (`2π/n` for
`2πn/N`), **56VI** (`b` for `a`), **81II.1** (`b𝒜` for `𝒜b`), **227III.4**
(inconsistent with 228II, which is right).

Two defects are in thesis **proofs**, not statements: **125II** computes
`#ℋ = Σ_ω #ℋ_ω` over an uncountable index set (the Lemma stands), and
**150XV** concludes `W = V̄` from *ultranorm* completeness where the Hilbert
module also needs *norm* completeness.  A third, **221IV.5**, asserts purity
of `h ∘ ξ` that its own proof never addresses.

### 2. Source housekeeping

**26II** gained a fifth item on 2026-08-19, but `asols.tex`'s `parsec-260.20`
still answers the old one — the new item 5 has no solution and the solution's
item 5 answers nothing.  And **eff.tex 199VII.4** is false as printed with its
`berr.tex` erratum *not* absorbed into the running text, while the parallel
correction for 197V.4 has been.

### 3. Questions already open, now with evidence

**B15** is decided as far as the tree goes — our definitions take eff.tex's
printed form verbatim, so under ruling (1) the single `sorry` in `VNExamples`
closes with no further mathematics.  **A6**'s knock-on is larger than
recorded (under the printed `DiscreteSpace`, 130V is false, 129VI vacuous,
127III gapped — and the repair orphans the thesis's own 129IV).  **A8**'s
recorded obstruction is gone (`dsumRep` exists).  **A9**, **A10**, **B13**,
**B14**, **D7** all confirmed as described; B13's weakness is in
`effectus_vn_partial`, *not* in `Effectus.lean`'s definitions, which are
faithful field by field.

### 4. Our statements to repair — needs an author ruling

The 174 `weaker` rows, dominated by three shapes: a **multi-part exercise
rendered by one clause** (much the commonest); an **isomorphism, or a
"has all X" headline, rendered by a witness or a consequence** (70III, 67IV.2,
69IVa, 84bV, 188III/188IV, 179III.1, 191II, 200III, 205II, 220II, 193V,
175III); and a **functor statement pinning only the object part** — which
QUESTIONS **B6** already had repaired for 192III.1/.2 in session 10, a repair
never carried across to `predMap_functor`, `stat_functor`,
`emod_effectus_representation` or `stat_mconvex`.

One clause is missing from the tree altogether while being *used*: **24II.4**
(reached through Mathlib).  **36II** was the other; it was stated on
2026-08-27 as `selfDual_hilbert`, and **36V** is no longer unused.  **191VIII.1**, **73III.4** and **101VII.1**'s middle
clause are simply absent.

The 49 `stronger` rows are mostly benign generalisations; the exception is
**139XI `ess_uniq_pur`**, which is **false as ours** — it drops all three
hypotheses the current `dils.tex` carries.  Its proof is `sorry`, so nothing
false is derived.

### 5. Proof routes resting on obsolete premises

**Four divergences are justified in-file by a "still `sorry`" that is no
longer true** — three in `A/Proc/Measurement` (63IV, 81VI/VII/IX, 98II) and
one in `A/Proc/Duplicators` (129X, on 51IX).  Each can now take the thesis's
route.  Several other `route` verdicts are deliberate and documented
(158II via the linking algebra, 208III avoiding the false 177Ia, `cauchy_formula`
via `polygon_winding`).

### 6. Stale prose — ours, and cheap to fix

Module headers reading "Statements only; every proof is `sorry`" on files with
none (`A/VN/Basic`, `A/VN/Completeness`, `B/Dils/{HilbertModules,
SelfDualCompletion, Stinespring}`); erratum notes claiming a fix is
outstanding when the source already carries it (`ncp_ceill`, `cceil_basic_2`,
two on 72III), and one describing a *superseded* version of its own gap
(33III, `centrally_similar_basic_3_meet_cceil_counterexample`); and a dozen
mislabelled DISPs (`31IV` for `30IV`; five one-point drifts in `VNExamples`;
`138II` for `138IV`; `154IV`/`154II` for `154V`; `216XI.Ax2`/`Ax3` for
`216XIII`/`216XIV`; `150IV` for 146V.3/146VII; `146VIII` for `146IX`).

## What happens to a finding

Nothing, immediately.  When the audit is complete the rows are triaged:

* a defect in the **thesis** → `ERRATA.md`;
* a question for the **authors** → `QUESTIONS.md`;
* a defect in **our transcription** → repaired, and logged in
  `PROVING-LOG.md` (`ERRATA.md`'s scope note excludes it);
* a **proof** that diverges without needing to → re-proved, or the divergence
  recorded in `PROVING-LOG.md` with its class.
