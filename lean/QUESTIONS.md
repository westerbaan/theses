# Questions for the authors

Everything in this file needs a decision from an author.  Nothing here is a
Lean problem: each item is either a defect in a thesis statement, or a choice
about how faithfully our statement should track the thesis.

Findings that need **no** decision live elsewhere: thesis defects to be
corrected are in [ERRATA.md](ERRATA.md), and our own mis-transcriptions in
[PROVING-LOG.md](PROVING-LOG.md).

**Everything in this file is open.**  Once a question is answered *and* the
answer is implemented, its section is **deleted** rather than marked resolved —
on 2026-08-16 that removed B2, B4, B5, B6, B7, D2, D3, B9 and the whole
"Resolved" section (821 → 345 lines).  The rulings themselves are preserved in
the commit messages that implemented them and in PROVING-LOG.md, so nothing is
lost; git history has the full text.  Do not re-add a resolved item.

Conventions: **DISP** is the display number (e.g. `192V.3`); erratum keys are
the `parsec-N.M` keys of the errata block at the top of `../asols.tex`.
Line references drift whenever the sources are edited — **locate by point
number, not by line**.

---

## Thesis B (`eff.tex`, `dils.tex`, `bsols.tex`) — all open

Thesis A was ruled on 2026-08-13; none of thesis B has been.

### B10. 158II `kaplansky-hilbmod` — **now proved, by a different route**; the printed proof (158III–158V) must be replaced
`dils.tex` parsec 1580.  The thesis proves 158II via **158V**, and 158V is
**false** (counterexample in `PROVING-LOG`/`ERRATA`; `B(ℓ²)`, `y = |e₂⟩⟨e₁|`,
`yₙ = |e₂⟩⟨e₁+eₙ|`).  **158II itself is true**: it is now proved in Lean
(`Theses/B/Dils/Kaplansky.lean`, 2026-08-16) through the **linking algebra**,
with no strengthening of its hypotheses.

**The proof.**  Let `Lk = X ⊕ ℬ` (a Hilbert ℬ-module) and work in the von
Neumann algebra `ℬᵃ(Lk)` (**152X** `ba_vonNeumannAlgebra`, which needs `Lk`
self dual).  Embed `X` in the corner by `cor z = |z ⊕ 0⟩⟨0 ⊕ 1|`, i.e.
`[[0,z],[0,0]]`.  Then

    (cor z)* (cor z) = ι⟨z,z⟩,    ι b = [[0,0],[0,b]],

so the ultrastrong seminorms of `cor z` are **exactly** the ultranorm
seminorms of `z` — the mirrored quantity `ω(bb*)` that kills every route
through 158V never appears.  `D` sits inside the closed ∗-subalgebra
`S = {T : T(N) ⊆ N and T*(N) ⊆ N}`, `N = cl(D) ⊕ 𝒜`, and the two hypotheses
of 158II are exactly what puts it there: `⟨D,D⟩ ⊆ 𝒜` (by polarization from
`⟨d,d⟩ ∈ 𝒜`) and `𝒜·D ⊆ D`.  Ultranorm density of `D` gives
`cor x ∈ ultrastrong-closure(S)`, thesis A's **74IV** `kaplansky` returns a
net in `S` bounded by `‖cor x‖ = ‖x‖`, and compressing at the vector `0 ⊕ 1`
lands in `cl(D)`; a norm approximation plus a rescaling `d ↦ t·d` puts it back
in `D` inside the ball (`kaplansky_hilbmod_of_closure`).

Three points worth recording, because they answer questions the earlier
analysis left open.

1. **`𝒜` need not be ultrastrongly dense in `ℬ`** (the hypothesis Lin's
   Theorem 4.4 needs and 158II lacks).  74IV is applied to a *single element*
   `cor x` and a subalgebra whose ultrastrong closure need not be everything.
2. **The self-adjointization `[[0,x],[x*,0]]` of the classical proof is not
   usable and not needed.**  Its square has the `|e⟩⟨e|` corner, which
   reintroduces the mirror (`θ_{e,e} = |e₂⟩⟨e₂|` is constant along the
   standard counterexample), so `ξ(dₙ) → ξ(x)` fails ultrastrongly.  Our
   `cor` is not self-adjoint, and 74IV — repaired in `A/VN` for exactly this
   reason — already handles non-self-adjoint elements.
3. **The only dependency is the self-dual completion 150II** `dils_completion`
   (parsec 1500, before 1580, so the thesis's own order is respected), used to
   pass from `X` to a self-dual `X̄`; ultranorm density is transitive, and both
   the norm bound and the seminorms are computed from the inner product, which
   the embedding preserves.  `150II` is still `sorry` in Lean, so
   `#print axioms kaplansky_hilbmod` shows `sorryAx`.  The **self-dual case**
   `kaplansky_hilbmod_of_selfDual` is unconditional and axiom-clean.

*Decision needed*: how to repair the thesis.  Concretely, 158III–158V should
be deleted or demoted, and the proof of `kaplansky-hilbmod` replaced by the
linking-algebra argument above (which the thesis has all the material for:
152X at parsec 1520, 150II at 1500, `kaplansky` at 74IV).  The erratum row for
158V in `ERRATA.md` carries the same request.

*Superseded material, kept because it rules routes out.*  The renormalizer
approach is dead for **every** renormalizer, not just the thesis's:

**Claim.** Let `φ : [0,∞) → ℝ` and `h(y) := y·φ(⟨y,y⟩)` (functional calculus —
the shape of every renormalizer of this kind, the thesis's `φ(t) = 2/(1+t)`
included).  If `‖h(y)‖ ≤ 1` for all `y ∈ X` and `h∘g = id` on the unit ball for
*some* `g`, then `h` is **not** ultranorm continuous.

*Proof.*  In `ℬ = B(ℓ²)`, `X = ℬ`, take `v ⊥ uₙ` with `‖v‖² = a > 0`,
`‖uₙ‖² = c > 0` and `uₙ → 0` weakly; put `y := |e₂⟩⟨v|`, `yₙ := |e₂⟩⟨v+uₙ|`
(all rank one, hence in `D = 𝒜 = K(ℓ²)`).  Since `⟨y,y⟩ = a·P_v` is rank one,
`φ(⟨y,y⟩) = φ(0)(1−P_v) + φ(a)P_v` and therefore `h(y) = φ(a)·y`; likewise
`h(yₙ) = φ(a+c)·yₙ`.  Now `⟨yₙ−y, yₙ−y⟩ = |uₙ⟩⟨uₙ| → 0` ultraweakly, so
`yₙ → y` ultranorm, while

    h(yₙ) − h(y) = (φ(a+c) − φ(a))·y + φ(a+c)·|e₂⟩⟨uₙ|,

whose second term is ultranorm null.  Continuity at `y` thus forces
`φ(a+c) = φ(a)` for **all** `a, c > 0`, i.e. `φ ≡ κ` on `(0,∞)`.  Then
`h(y) = κy` for every `y ≠ 0`, so `‖h‖` is unbounded on `X` unless `κ = 0`,
and `κ = 0` contradicts `h(g(x)) = x` for `x ≠ 0`. ∎

The scheme asks one continuous function to be *sensitive* to the escaping mass
(to contract into the unit ball) and *insensitive* to it (to be ultranorm
continuous) at once; restricting `h`'s continuity to points `g(x)` or to nets
from `D` does not help, since the counterexample already lies inside that
restriction.  Also recorded: iterated trimming fails because the accumulated
coefficient `1 − q_{k-1}⋯q₀` is an ordered product of noncommuting positive
contractions and can exceed the unit ball (`‖·‖ ≈ 1.155` for two ideal
trimmers) — there is no two-sided trimming on a one-sided module.  H. Lin,
*Double duals and Hilbert modules*, arXiv:2311.15462 §4 proves an analogue
under two hypotheses 158II lacks (`𝒜` SOT-dense in `M`; the target in the
norm-closed `M`-module generated by `D`); the linking-algebra proof needs
neither.  `kaplansky_hilbmod_of_weak` (158II from *weak* bounded
approximation) and `kaplansky_hilbmod_of_commutative` remain in the file as
independent partial results.

### B11. 169VIII `dils-def-filter` — "filter **for** `b`" is defined weaker than in proc.tex, and 169XI.2 is false as printed
`dils.tex:6118`.  The Definition says "`c` is a filter for `b ≥ 0` if
**`c(1) ≤ b`** and every ncp-map `f` with `f(1) ≤ b` factors uniquely through
`c`", while proc.tex **96I** (`filter`), which the surrounding text says it is
recalling, asks the universal property for `f(1) ≤ c(1)` and calls `c` a filter
*for `c(1)`* — so there `c(1) = b` by construction.

The two are genuinely different: `c = ½·id : ℬ → ℬ` satisfies the dils.tex
condition for `b = 1` (each `f` with `f(1) ≤ 1` factors uniquely, as `2f`)
while `c(1) = ½`.  Consequently **169XI**.2 — "there is a unique **unital**
ncp-map `φ'` with `φ = c' ∘ φ'`", for `c'` a filter of `φ(1)` — is false as
printed: take `φ = id : ℂ → ℂ` and `c' = ½·id`.  Its `bsols.tex` solution uses
`c'(1) = φ(1)`, i.e. the proc.tex reading.  See ERRATA for the one-character
fix (`c(1) ≤ b` → `c(1) = b`), which repairs everything; the *derived* notion
"`c` is a filter" (= a filter for some `b`) is insensitive to the change, so
purity (**170I**), **169XI**.1 and **169XII** are untouched.

*Decision needed*: our `IsFilterFor` (`B/Dils/Pure.lean`) transcribes
dils.tex literally and so carries the weak form, which leaves
`dils_filter_basics_2a` unprovable.  Say whether to change it to `c 1 = b`
(the proc.tex form) — we have not, under the standing rule that statements are
not altered without an author's ruling.

*Status 2026-08-16 (worker 73): the blast radius is now **machine-confirmed**
to be exactly `dils_filter_basics_2a`.*  **169XI**.1 `dils_filter_basics_1`
and **169XI**.2's second half `dils_filter_basics_2b` are both **proved**
against the weak (dils.tex) reading and are axiom-clean.  Part 1 survives
because the only place it needs the filter's universal property is at
`h'(1) = c(φ(1))`, and `c(φ(1)) ≤ c(1) ≤ b` holds under either reading; part
2b never uses unitality of `φ'` at all — it is part 1 applied to `c'` and the
dilation of `φ'`.  So a ruling on B11 changes exactly one Lean statement.

### B12. 139XI `ess-uniq-pur` — essential uniqueness of purification is false without a dimension hypothesis; which repair?
`dils.tex:998`, solution `bsols.tex:209`.  The exercise asks to show: if
`V, W : 𝒦 → ℋ ⊗ 𝒦'` satisfy `V*(a⊗1)V = φ(a) = W*(a⊗1)W` for all `a ∈ B(ℋ)`,
then `V = (1 ⊗ U)W` for a **unitary** `U` on `𝒦'`.

**Counterexample** (see ERRATA for the full row): `𝒦' = ℓ²`, `𝒦 = ℋ ⊗ ℓ²`,
`W = 1`, `V = 1 ⊗ S` with `S` the unilateral shift.  Both dilate
`φ(a) = a ⊗ 1`; the only `U` with `V = (1⊗U)W` is `S`, which is an isometry
but not unitary.  Weakening "unitary" to "isometry" does not save it either:
exchanging `V` and `W` in the same example requires a `U` mapping `𝒦'` onto
`𝒦'` isometrically *from* a proper subspace, which is impossible.

The solution is correct up to its last paragraph, which reads "As `𝒱` and `𝒲`
are isomorphic, they have the same dimension and so do `𝒱^⊥` and `𝒲`" (the
last `𝒲` is a typo for `𝒲^⊥`).  Equal dimension does not imply equal
codimension in infinite dimensions, and that is exactly what the extension of
`U₁ : 𝒲' → 𝒱'` to a unitary of `𝒦'` needs.

*Decision needed*: point 139X introduces the property as one "concerning
dilations *of the same dimension*", so a hypothesis is clearly intended.
Which one — (a) both dilations minimal, (b) `dim 𝒦' < ∞`, or (c) conclude only
with a unitary `𝒲' → 𝒱'` between the ancilla subspaces?  Under (a) or (b) the
printed statement is recovered verbatim; under (c) the exercise's own first
half is already the whole content.  We have left `ess_uniq_pur` `sorry`ed and
unchanged.

### D6. 164II.2b `ext_tensor_ketbra_dense` — **our** statement is false; the thesis's is true and is now proved
`dils.tex:5327` (**164XI**), `SelfDual.lean`.  The thesis claims only that the
linear span of

>  `D = {|(e'ᵢa) ⊗ (d'ⱼb)⟩⟨e_k ⊗ d_l|; a ∈ 𝒜, b ∈ ℬ, i,k ∈ I', j,l ∈ J'}`

is **ultraweakly dense** in `ℬᵃ(X ⊗ Y)`.  Our transcription instead demands an
approximating **net indexed by `Finset (ι × κ)` along `atTop`** (copying the
shape of **159IV** `ketbra_ultraweakly_dense`, where the thesis's own proof
*does* produce such a net, `p_S T p_S`).  That strengthening is **false**:

* take `ι = κ = PUnit`, `𝒜 = ℬ = B(ℓ²)`, `𝒞 = 𝒜 ⊗ ℬ`, `X = 𝒜`, `Y = ℬ`,
  `E = extTensorSelf` (session 52), `e = d = 1` — a legitimate orthonormal
  basis of a von Neumann algebra over itself;
* then `E.Z = 𝒞`, `f() = t 1 1 = 1`, `ℬᵃ(X ⊗ Y) ≅ 𝒞` (as right multiplications)
  and `span D ≅ 𝒜 ⊙ ℬ`, the *algebraic* tensor product;
* `Finset (PUnit × PUnit)` has a greatest element, so `atTop` is the principal
  filter there and — the ultraweak topology being Hausdorff — the net's value at
  that element must **equal** `T`.  So the statement would force
  `𝒜 ⊗ ℬ = 𝒜 ⊙ ℬ`, which fails for `B(ℓ²)`.

The counterexample cannot be written down *inside* the tree, because
`IsVNTensor` is axiomatized (proc.tex 108II is not formalized) and the only
concrete instance we have is `ℂ ⊗ ℂ = ℂ`, where the statement is true.  So the
`sorry` is left in place per the never-change-a-statement rule.

**The thesis's actual claim is now proved**, as `ext_tensor_ketbra_uwDense`
(same file, immediately below), in the entourage form "for finitely many
np-functionals and `ε > 0` there is an element of `span D` within `ε` of `T` on
all of them" — via **159IV**, **164II**.2a, Kaplansky (**74IV**) and **159IX**
(also proved this session).  That form is what **165VI**'s `generates` clause
needs, so nothing downstream is lost.

*Decision needed*: replace the net in `ext_tensor_ketbra_dense` by the
entourage form (i.e. delete the statement and keep `ext_tensor_ketbra_uwDense`
under the 164II.2b name), or keep both with the net form restricted to a
hypothesis that rules the degenerate case out.  We recommend the first.

### B8. Minor: `bsols.tex`'s `onb1` solution over-assumes
Its solution assumes self-duality, which neither the exercise nor our statement
requires.  Harmless; noted for tidiness.

---

## Thesis A (`cstar.tex`, `vn.tex`, `proc.tex`) — remaining after the 2026-08-13 rulings

### A1. 98VI's hint points the wrong way
`proc.tex:631`.  The hint says to show `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥`.  That is a
restatement of `τ(π(r^⊥)) = 0` and is the direction one does **not** need; the
proof requires the **converse**, `⌈τ⌉^⊥ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉`.  In the concrete model
both hold (the two sides are equal), so nothing downstream is wrong — but only
the converse is usable.

⚠️ **Update (session 48): 98VI is now proved, and it needs neither the hint nor
its converse**, so this is a question about the *hint* only.  The exercise is
short if one takes the corner's effect to be `s := β'(r)` rather than the
carrier `⌈τ∘π⌉` — see the 98VI row of ERRATA.md for the four-line argument.
The decision left is whether to replace the hint by that route or to keep the
carrier route with the inequality turned round.

### A5. 81IX `div-usc` — the second half is false; which repair do you want?
`vn.tex:5533`.  The Lemma claims both `a ↦ a/b : (𝒜)₁b → 𝒜` **and**
`a ↦ c∖a/b : c(𝒜)₁b → 𝒜` are ultrastrongly continuous.  The first is true and
is now proved from the thesis's own argument (`div_usc_ball`).  The second is
**false** — see the 81IX row in ERRATA.md for the counterexample
(`b = 1`, `c = diag(1,½,⅓,…)` in `B(ℓ²)`, `dₙ = |n⟩⟨0|`).

Three repairs are available and they are not equivalent, so this needs a
decision:

1. **Drop the second map.**  Nothing in **vn.tex** appears to use it: the
   sequel (**82I** polar decomposition, **83II**, **83V**) uses only
   **81III** and the definition of division.  ⚠️ **Update (session 47):** it
   *is* used, in **proc.tex** — the proof of **96V** `canonical-filter`
   derives normality of `g = d*∖f(·)/d` from precisely this false half.  96V
   itself is true, and its proof has been repaired (and machine-checked)
   without any form of `div-usc`: see the **96VI** row of ERRATA.md.  So
   option 1 remains available, but it needs the 96VI repair alongside it.
2. **Restrict `c`.**  For `c` with closed range — equivalently `c`
   pseudoinvertible in the sense of **79I** — one has `c∖x = tx` for the
   bounded pseudoinverse `t`, and `‖t(x−x₀)‖_ω ≤ ‖t‖‖x−x₀‖_ω` makes the map
   continuous at once.
3. **Weaken the topology for that factor** to the ultrastrong-\* topology,
   in which `c∖(·)` *is* continuous on `c(𝒜)₁` (the mirror of the thesis's
   own argument, run on the seminorms `ω(xx*)^½`).

Note that **81VII** `div-approx` — which reads like the same statement about
`c∖·/b` — is **true** and is proved (`div_approx`): for one fixed `a` the
convergence holds by normality; it is only the *uniformity* over the unit ball
that fails, and the Lean statement of 81VII does not claim it.  The thesis's
parenthetical "(and uniformly so)" in 81VII should therefore be checked too:
by the same counterexample it is false for the `c∖·` half.

### A6. 129II.2 `discrete` is weaker than "purely atomic"; 130V is false as printed — which repair?
`proc.tex:6188`.  129II.2 defines a finite complete measure space to be
**discrete** when it is *covered by atomic measurable subsets*, and asserts
parenthetically that this coincides with Fremlin 211K's *purely atomic*.  It
does not: with `X = [0,1]` and `μ = λ + δ₀` (completed) the sets `{0,x}` are
atoms and cover `X`, yet `(0,1]` has positive measure and includes no atom.
For that `X`, `L^∞(X,μ) ≅ L^∞[0,1] ⊕ ℂ`, so **130V** `discrete-ell-x`
("a discrete finite measure space has `L^∞(X) ≅ ℓ^∞(Y)`") is **false as
stated** — see the 129II.2 row of ERRATA.md.  The Lean statement transcribes
129II.2 verbatim, so `discrete_ell_x` is unprovable and is parked.

The repair we expect is to replace the definition by Fremlin's ("every
non-negligible measurable set includes an atom"), but that is a *statement*
change and touches three further points, so it needs a ruling:

1. **129VI** `measure-space-continuous-discrete` is *true* as stated but
   **vacuous** under the printed definition (in the counterexample `D = univ`
   satisfies both conjuncts).  With the repaired definition its Zorn argument
   goes through if `𝒮` is taken to be *countable disjoint unions of atoms*
   rather than *sets covered by atoms*.
2. **130V** becomes provable, by the route the Lean tree already has: 130IV
   `measure-space-partition` is proved, and `atomic_measure_space` turns each
   atom into `ℂ`.
3. **127III** `duplicable`, the main theorem of the chapter, is proved at
   proc.tex:6543 from 129VI + 129X + 130V, so its proof has a gap as printed.
   The theorem itself is not in doubt.

Do you want the definition repaired (and 129VI's proof adjusted), or 130V
restated with the stronger hypothesis carried explicitly?

### A2. `parsec-340.60` (34VI.1) is an empty `\TODO{}`
The solution slot exists but is empty, and it is the *last* entry in
`asols.tex` — which is why solution coverage appears to stop at parsec 340.
Our `cstar_product_4` is proved, but from Mathlib rather than the author's
argument, so it is **not cross-checked**.

### A3. Statements the theses only *cite*, never prove
These have no proof to transcribe, so we have parked rather than proved them.
Confirm that is the right treatment:

* **179III.2** Gudder–Pulmannová representation (`eff.tex:739`, cited to
  `gudder1998representation`).  Note our statement is also *weaker* than the
  cited result — it omits both the order-unit condition and the scalar
  compatibility — so if it is ever revived it must be strengthened first.
* **178III.2** "every finite effect monoid comes from a Boolean algebra, hence
  is commutative" and **178III.4** "there is a non-commutative effect monoid on
  lexicographic `ℝ⁵`" (`eff.tex:640`/`651`, cited to `basmsc` prop. 40 /
  cor. 51).  Three parked statements: `finite_effectMonoid_boolean`,
  `finite_effectMonoid_commutative`, `exists_noncommutative_effectMonoid`.
* **192V.4** "every cancellative abstract `[0,1]`-convex set embeds affinely in
  a real vector space" (`eff.tex:2591`, cited to `statesofconvexsets` thm. 8);
  `cancellative_iso_convex`.
* ~~**`extensive_effectus`**~~ (189aII.3, `eff.tex:2043`, cites `effintro`) —
  **no longer parked: proved 2026-08-14** (worker 44) from Mathlib's
  `FinitaryExtensive`, i.e. from the van Kampen property of binary coproducts.
  Two remarks for the authors, since this is the one place where we had to
  supply mathematics the thesis does not contain:
  * The two pullback axioms are essentially immediate from extensivity, as one
    would expect.  The **third** axiom — joint monicity of
    `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 → 1+1` — is *not* proved anywhere in
    `eff.tex` or `bsols.tex`, and Mathlib has nothing about it either.  It is
    **true** in any finitary extensive category with a final object; the short
    argument is in PROVING-LOG session 17 and is now formalized.  It may be
    worth a sentence in the text, since the reader is otherwise left with the
    hardest of the three axioms unaddressed.
  * `effintro` is still the only citation; we did not consult it.  If it does
    contain the argument, our proof is an independent one and the entry above
    can simply be dropped.
* **`effectus_vn`** (`eff.tex:832`, says only "adapt the proof of
  `emod-effectus`").  Note (2026-08-14, worker 45): `emod-effectus` (191II) is
  now fully formalized, so the analogy now has something concrete to be an
  analogy *to* — but the two proofs share nothing beyond their shape: 191II's
  is elementwise in `EMod_M`, and the `vNᵒᵖ` version needs the von Neumann
  theory of thesis A, none of which is on `B/Eff`'s import path (`B/Eff`
  imports only `Theses.Common`).
* **177Ia** — see B4 above.

### A4. 217I's independence-of-choice claim is not formalised
Our `IsDaggerOf` is stated relative to the *chosen* `π_{IM f}`, so the theorem
as transcribed does not assert that the dagger is independent of that choice —
which is what 217I is about.  Not wrong, but weaker than the source.  Low
priority; flagged so it is not mistaken for a full formalisation.

---

## Not for the authors — upstream Mathlib

Recorded here only so they are not re-diagnosed.

* `ContinuousFunctionalCalculus ℝ (CStarMatrix n n 𝒜) IsSelfAdjoint` and
  `NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix …)` / `NonnegSpectrumClass ℝ`
  **are not found by instance search** although they apply verbatim: the
  instance carries `Algebra.complexToReal` while `Algebra ℝ (CStarMatrix …)`
  resolves to `CStarMatrix.instAlgebra` — defeq but not syntactically equal.
  Worked around with `letI` throughout; worth filing upstream.
* Mathlib has **no double commutant theorem** (an explicit TODO in its own
  header), **no von Neumann tensor product**, no spatial tensor product, and no
  normal GNS.  Its `VonNeumannAlgebra` is the *concrete* (double-commutant)
  definition; `WStarAlgebra` is Sakai-style — neither matches the thesis's
  Kadison-style abstract definition.

---
