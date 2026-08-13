# Errata — defects in the theses, for processing

One line of context per item, ordered by point number within each thesis, so
this file can be worked through top to bottom.  **Status** is `OPEN` (not yet
acted on by an author) or `DONE` (fixed in the sources; erratum key given where
one exists).

Scope: **only defects in the theses**.  Our own mis-transcriptions are *not*
here — they are in [PROVING-LOG.md](PROVING-LOG.md), since they need no author
attention.  Items needing an author **decision** rather than a correction are in
[QUESTIONS.md](QUESTIONS.md).

Locate by **point number**, never by line: `file:LINE` references drift every
time the sources are edited.

---

## Thesis A — `cstar.tex`

| # | defect | fix | status |
|---|---|---|---|
| **4VIII** | inner product typed `⟨x,·⟩ : V → V` | codomain is `ℂ` | DONE `40.80` |
| **11VI.2** | bound stated as `‖a‖ < ‖b‖` | should be `‖a‖ < ‖b⁻¹‖⁻¹` | DONE |
| **11XV.2** | "invertible **by point 2**" is a self-reference | it is point 1, cited correctly 30 lines later | DONE (solution) |
| **11XV.3** | hint `aⁿ+1 = ∏(a+ζ^{2k+1})` has the wrong sign | RHS is `aⁿ−1`; should be `∏(a−ζ^{2k+1})` | DONE (pre-existing) |
| **11XV.3** | "`ζ^{2k+1} ∉ ℝ` when `k ≠ ½(n−1)`" | should be `k ≢ (n−1)/2 mod n`; literally false at `n=1` | OPEN (harmless) |
| **11XX.1** | `f : X → ℝ`, but `C(X)` is the complex-valued functions | `f : X → ℂ` | DONE `110.200` |
| **11XX.2** | "invertible iff its kernel is **not** `{0}`" — dropped negation | `A = 0` in `M₁` refutes it as printed | DONE (solution) |
| **12III.3** | `z ∈ 𝒜` | should be `z ∈ ℂ` | DONE `120.30` |
| **16V** | false in the trivial algebra `{0}` (every element a unit, `spec = ∅`) | hypothesise `𝒜 ≠ {0}` | DONE `160.50` |
| **16VI** | same defect in the `←` direction | reworded: `spec(a) ⊆ {λ}` iff `a = λ` — true in `{0}` too | DONE `160.60` |
| **17III** | stated for `t ∈ [0,∞]`; at `t = ∞` the condition is meaningless | `[0,∞)` | DONE `170.30` |
| **17VI.3** | `inf` over `λ ∈ ℝ` is `−∞` in `{0}` | `inf` over `λ ≥ 0` | DONE `170.60` |
| **17VI.6** | "suppose `a` is **not** invertible" inverts the direction proved | delete the "not" | DONE (solution) |
| **19Ia** | `λ⁻¹(1 + b(λ−ab)a)` missing an inverse | `λ⁻¹(1 + b(λ−ab)⁻¹a)` | DONE `190.20` |
| **20aII** | "`e ∘ h = g`" | should be `γ` | DONE (solution) |
| **20II.1** | proof needs `f a` self-adjoint, never stated; not part of `IsPositiveMap` | derive from `a = a⁺ − a⁻` | OPEN |
| **22III.5** | false in `{0}`; the solution also picks a convergent subsequence of `spec(a)`, assuming it non-empty | hypothesise `𝒜 ≠ {0}`, cite 16V | DONE `220.30` |
| **22VIII** | state-existence half false in `{0}` | hypothesise `𝒜 ≠ {0}` | DONE `220.80` |
| **23II** | cites `ineq-square-root` where commuting products are handled | cite `square-commuting-monotone` (230.40) | DONE `230.60` |
| **23VII.3** | "commuting `a ≤ b` ⟹ `a² ≤ b²`" false: `a = −2 ≤ 1 = b` in `ℂ` | assume `0 ≤ a ≤ b` | DONE `230.70` |
| **26II.1** | "`a` and `b` are positive" — `a` is arbitrary self-adjoint; and `b ≥ 0` is used but not derived | add the step `2b = (b−a)+(b+a) ≥ 0` | DONE (solution) |
| **26II.4** | `a ∨ b = ½(a+b+|a+b|)` | should be `|a−b|`; check `a=2, b=−1` | DONE (solution) |
| **30IV.1** | Cauchy–Schwarz displayed with squares on the right | as printed it does not give Kadison's inequality | DONE (solution) |
| **30IV.2** | spurious `‖ω‖` factor | Mathlib's `leftMulMapPreGNS` has bound exactly `‖a‖` | DONE `300.40`/`300.60` |
| **32I** | definiteness stated once, but used in the *first* argument for module-linearity and the *second* for uniqueness of the adjoint | state both | OPEN |
| **33I.2** | the surjectivity half never uses the adjointability hypothesis | redundant, harmless | OPEN |
| **34aVII** | Russo–Dye false at `N = 0` (Lean's `2/0 = 0` makes the hypothesis vacuous) | "for some natural number `N > 0`" | DONE `341.70` |
| **34VI.1** | solution slot `parsec-340.60` is an empty `\TODO{}` | — | OPEN |
| **34XVI** | derives `cp-russo-dye` from Russo–Dye (**34aVIII**), a *later* point | forward reference; we derive it from 34XIV instead | OPEN |
| **39VII** | `ω(A) = ∑_{e,e'∈E} ⟪e,Ae'⟫ ω(\|e⟩⟨e'\|)` is **false** if `∑` means the unordered sum of 6II: the family need not be absolutely summable (`ω = ⟪x,(·)x⟫` on `ℓ²`, `A` block diagonal with `N_k×N_k` DFT blocks, `N_k = k⁸`, `x` constant `k^{-5}` on block `k`) | read it as the limit of the **square** partial sums `∑_{e,e'∈F}`, `F ⊆ E` finite — which is what the proof establishes and what 39IX uses; our statement is realigned and **proved** | OPEN |
| **62I** | cites `inner-product-basic` for `f(a)² ≤ f(a²)` | should cite `cp-cs` | DONE `620.20` |
| **9II** | on `X = ∅` the "iff" in the `sup ∅` step fails for `t < 0` | harmless — only two directions are used | OPEN (nit) |
| **7III.8 / 7III.13 / 9X.3** | counterexample solutions open "let `x,y` be … vectors" without exhibiting one | needs `dim ℋ ≥ 2`; `ℂ²` works in all three | OPEN (nit) |
| **9X.3** | divides by `‖P − ‖x‖²‖` without excluding zero | degenerate case is fine anyway | OPEN (nit) |

## Thesis A — `vn.tex`

| # | defect | fix | status |
|---|---|---|---|
| **37IX** | "is WOT-Cauchy **and WOT-bounded**" does not follow: 37VII needs *norm*-boundedness, 37IX supplies only a bound from above (`D = {−n·1}`) | statement gains "non-empty"; proof squeezes boundedness, gets self-adjointness via 25V(1). **37VII deliberately unchanged** | DONE `370.90`/`370.100` |
| **37IX** | omits `D ≠ ∅`, needed by parts 1 and 2 | — | DONE (as above) |
| **37IX** | proof claims 37VII yields a *self-adjoint* limit; 37VII concludes only "some bounded operator" | — | DONE (as above) |
| **38VI.2** | `←` direction false: a constant net `x_α = i·x` gives the same vector functional | direction dropped; our statement realigned and the surviving implication **now proved** | DONE `380.60` |
| **44III** as cited by **44VII/44XIV** | cited as a black box, but it demands *every* `xᵢ` be an effect, while `(⋁D − d)/M` is only *eventually* one — a bounded directed set need not be bounded below | needs a cofinal-tail footnote once nets are made precise | OPEN |
| **61II** | both displayed inequalities point the wrong way | reversed, as is the proof's last line | DONE `610.20` |
| **68IV.2** | clauses 1 and 3 stated without positivity; central support is monotone only on positives (`D = {−1,0}`; `a=1, b=−1`) | positivity added to both | DONE `680.40` |
| **72III.1b/1c** | spurious `‖ω‖`: `‖a‖_ω` is unnormalised, so the two sides scale as `t` and `t²` | factors deleted | DONE `720.30` |
| **75III** | proof asserts `0 ≤ a_nm ≤ ½` | should be `0 ≤ a_nm ≤ 1` | DONE `750.30` (solution) |
| **89I** | "`UU* = FF*` is the projection onto `closure(π(A)y)`" | must read `U*U = FF*` | OPEN |
| **89III** | declares `Uᵢ : H → K`, then swaps the two projections and later writes `⟨x, Uᵢy⟩` as if `Uᵢ : K → H` | make the typing consistent | OPEN |
| **99VII** | three `a`-for-`b` slips at 61II's sole use site | corrected paragraph | DONE `990.70` |

## Thesis A — `proc.tex`

| # | defect | fix | status |
|---|---|---|---|
| **98VI** | the hint gives `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`, which is a restatement of `τ(π(r^⊥)) = 0` — the direction one does *not* need | the proof needs the converse; both hold in the model | OPEN |

---

## Thesis B — `eff.tex` / `bsols.tex`

| # | defect | fix | status |
|---|---|---|---|
| **175II.4 / 175V.7 / 181IV.1 / 181XIII / 183III.1 / 195V.1 / 211XVI / 225VI** | assorted session-1 findings | see PROVING-LOG for each | OPEN |
| **177Ia** | proof uses `x⊥ ⋁ s` for an arbitrary upper bound `s`, but that sum is only defined when `s ≤ x` — so it proves leastness only *below* `x`. **Not repairable** in a general effect algebra (needs a Riesz decomposition step); the result is only *cited* (Dvurečenskij–Pulmannová 1.8.2) | see QUESTIONS.md B4 — it is no longer load-bearing (nothing in B/Eff depends on it) | OPEN |
| **178III.1** | the uniqueness claim "(This is the only way to turn `[0,1]` into an effect monoid)" is asserted by citation only (`basmsc` prop. 41) | **no defect: it is true.** Now proved in Lean from the effect-monoid axioms alone — one-sided distributivity makes `y ↦ a ⊙ y` additive and monotone, and Cauchy's functional equation gives `a ⊙ y = a·y` | OPEN (informational) |
| **178IIIa** | uses one-sided distributivity, not an effect-monoid axiom | the four-fold law of 178II leaves exactly the terms to vanish; note one-sided distributivity *is* derivable, but only **after** `a ⊙ 0 = 0`, which is what the exercise asks for — so the solution as written is circular, not merely under-justified | OPEN |
| **178IIIa** | the exercise reads "Show that `a ⊙ 0 = a = 0 ⊙ a`" | typo: `a ⊙ 0 = 0 = 0 ⊙ a` (as printed it is false in `[0,1]`) | OPEN |
| **178IIIa/178IV** | the unnumbered point 40 ("Later, in a tangent, we will need the following specific fact about effect monoids") is `\begin{point}`-nested **inside** the exercise point 31, so it displays as a sub-point of `exc-emonzero` instead of as 178IV introducing 178V | move the `\end{point}` of point 31 before point 40 | OPEN (nit) |
| **179III.2** | Gudder representation is asserted by citation only | nothing to transcribe — parked | OPEN |
| **186IV** | states the pullback square only in its `▷₁` form, but 186X's proof needs `▷₂` too | state both | OPEN |
| **186VIII.2** | uses a `κ₂` form of a pullback axiom stated only for `κ₁` | — | OPEN |
| **189I.2** | swaps "total form" and "partial form" | — | OPEN |
| **192V.3.3** | "semilattices are exactly abstract 2-convex sets" is **false**: by Def. 192II the support uses the *partial* sum and `1 ⋁ 1` is undefined in `2`, so `𝒟_2 ≅ Id` and they are just sets | holds for the non-empty-finite-powerset monad; see QUESTIONS.md B1 | OPEN |
| **194I** | "As `𝒟_M ∅ = ∅`, the empty set is trivially also an abstract `M`-convex set and in fact the initial object of `AConv_M`" is **false for the trivial effect monoid** `M` (`1 = 0`): there the only formal convex combination is the empty one, so `𝒟_M ∅` is a *singleton*, admits no `h : 𝒟_M ∅ → ∅`, and `∅` is not an object of `AConv_M` at all | the proposition survives — for `1 = 0` every object of `AConv_M` is a singleton, so `1` is initial; add the case split (or assume `1 ≠ 0` for effect monoids). Formalized with the split | OPEN |
| **195VII** | rests on a false step: "if `c⊙a ⊥ c⊙b` then `(c/c)⊙a ⊥ (c/c)⊙b`" fails in `[0,1]` at `c = ½`, `a = b = 1` | statement is true; our proof takes another route | OPEN |
| **eff.tex:414 and the `exc-dposet` solution** | **partial associativity used backwards**: from `a ⊥ (c ⋁ d)` they conclude `a ⊥ c`, which the PCM axioms do not give | recoverable; we added `PCM.assoc_left` | OPEN |
| **208III** | the proof takes `s ⋁ t = s ∨ t` from `ea-modularity-prop` (177Ia, gapped) and orthomodularity from `orth-ea-is-orthomodular` (177VI, which also rests on 177Ia) | both detours are avoidable: sharpness alone gives `s ⋁ t ≤ s ∨ t` (a predicate is `≤` a sharp `j` iff it vanishes on `π_{jᵖ}`), and the orthomodular law follows from `ovee_le_of_le` + 208IX/208XII — formalized this way, which is what removed the last `sorryAx` leak from B/Eff | OPEN |
| **221II** | in the definition of a dilation, the mediating map is typed `h' : X → P` | must be `X → P'`, or `ϱ' ∘ h'` does not typecheck | OPEN |
| **221IV.6** | never checks that the mediating map is *pure*, though 221II requires it | true; we have now proved it | OPEN |
| **226II** | the proof builds a pristine `l` and computes `asrt_{s&tᵖ}² = asrt_{s&tᵖ}` to show `s & tᵖ` is sharp — but the hypothesis gives `tᵖ ≤ s`, so **213V** yields `s & tᵖ = tᵖ` in one step | cite `simple-andthen-absorption` instead; the rest of 226II then needs no dagger at all | OPEN (nit, but it shortens a page) |
| **226VII** | uses `m†` and "comprehensions are †-mono" / "`m†` is sharp" | the `ζ` of 211VII does the same job without the dagger development | OPEN (nit) |
| **227III.1** | exactness at `B` given as `IM^⊥ f = ⌈1∘f⌉` — does not mention `g` at all | must be `⌈1∘g⌉`; our corrected form is proved and the printed one is false | OPEN |

## Thesis B — `dils.tex` / `bsols.tex`

| # | defect | fix | status |
|---|---|---|---|
| **139VII** | finishes by citing an external source (`westerbaan2016universal`, lem. 9) | we found a citation-free substitute reusing the author's own identity | OPEN (nit) |
| **165III** | needs positivity of `Mₙ(⊗)` (`cp-bilinear`), which the definition of a vN tensor product does not provide | see QUESTIONS.md B5 — needs a positivity clause | OPEN |
| **`onb1` solution** | gratuitously assumes self-duality, which neither the exercise nor the statement needs | — | OPEN (nit) |

---

## How these were found

Worth recording, because it shaped the method: **proving a statement finds
nothing.**  Every erratum above came from *comparing* our proof with the
author's.  Two dedicated audits — re-reading the authors' arguments for
statements already proved from Mathlib — produced **10 errata between them**,
after which the workflow was inverted to "transcribe the thesis's proof first,
Mathlib only as fallback".

The single most productive check is reading a declaration against the
`file:LINE` its own doc comment carries.  The second is reading it against its
own doc-comment *prose*, which has caught a false statement with no reference to
the source at all.
