# The commutation theorem — the costing that preceded its proof

*A dated record.  Reconnaissance of 2026-08-25, four independent passes:
Mathlib's inventory, the tree's inventory, what the seven then-blocked
statements needed, and the shortest correct proof in the literature.  The
theorem was then built (`Theses/A/Proc/Commutation*.lean`,
`Theses/A/VN/Tomita*.lean`, `Modular*.lean`, `StandardSubspace.lean`) and
every statement it blocked is proved; the current state of any declaration
named below is in the tree, not here.  Kept because it explains why the
development has the shape it has.*

Read with `PROVING-LOG.md` session 83, which first established the equivalence
recorded in §1.  (The `docs/why-open.csv` rows `intersection_tensor` and
`equaliser_lemma` were deleted on 2026-08-26, when both statements closed; see
the banner in §1.)

---

## 0. The thesis says this one out loud

`a.tex:274`, in the introduction to thesis A:

> I've not just mixed and matched results from the literature, but I tailored a
> thorough treatise of everything that's needed, **including proofs (except
> `intersection-tensor-proof`)**.

`intersection-tensor-proof` is the single exception in the whole of thesis A.
`proc.tex:4473` is one line — *"Proof. See Corollary IV.5.10 of [Takesaki1]."*
The one point the thesis declines to prove is the one point still blocking us.
That is a fact about the subject, not about the formalization.

## 1. Everything blocked is blocked on one theorem

> **All seven closed, 2026-08-26.**  `Theses/A/Proc/QuantumLambda.lean` is
> `sorry`-free, and with it the whole of `Theses/A/Proc`.  The last five —
> 125VI `tensor_equalisers`, 125VIIb `tensor_preimage`, 125VIII
> `tensor_closed`, 125eIIa `tensor_map_factorisation` and 125eIII
> `tensorBsurjectivity` — went in one round on top of 121II and 125IV; see
> §7 for what that round found, including two places where the plan named
> the wrong hard step.
>
> **Closed, 2026-08-26.** 121II `intersection_tensor` and 125IV
> `equaliser_lemma` are **proved**; the count below is now **five**, not seven.
> The last obstacle was not mathematics but the import graph: `A/Proc/
> Commutation.lean` imported `QuantumLambda.lean`, so the finished commutation
> theorem sat *above* the statement it proves.  `concreteTensor` and its API,
> `uwTendsto_of_isLUB` and `uw_compress_tendsto` — the only things
> `Commutation.lean` used from `QuantumLambda.lean` — moved down into
> `A/Proc/Tensor.lean`; `Commutation.lean` now imports `Tensor.lean`, and
> `QuantumLambda.lean` imports `A/Proc/CommutationTheorem.lean` and discharges
> 121II with `intersection_tensor'`.  125IV followed: the development that was
> `A/Proc/EqualiserLemma.lean` (which had had to copy ~310 lines of
> `QuantumLambda.lean`'s `private` auxiliaries verbatim in order to see them)
> moved into the end of `QuantumLambda.lean`, the copies were deleted, and
> `EqualiserLemma.lean` no longer exists.  The rest of this section is the
> 2026-08-25 reconnaissance, kept for the record.

Seven `sorry`s remained in `Theses/A/Proc/QuantumLambda.lean`:

| point | name | line | status |
|---|---|---|---|
| 121II | `intersection_tensor` | :314 | **proved 2026-08-26** |
| 125IV | `equaliser_lemma` | :2032 | **proved 2026-08-26** |
| 125VI | `tensor_equalisers` | :2060 | **proved 2026-08-26** |
| 125VIIb | `tensor_preimage` | :2085 | **proved 2026-08-26** |
| 125VIII | `tensor_closed` | :2116 | **proved 2026-08-26** |
| 125eIIa | `tensor_map_factorisation` | :4727 | **proved 2026-08-26** |
| 125eIII | `tensorBsurjectivity` (`mpr` only) | :4758 | **proved 2026-08-26** |

121II is Takesaki I, Cor. IV.5.10, and is **equivalent** to Thm IV.5.9, the
commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'`, given the double commutant theorem —
which we have. Both directions re-verified independently on 2026-08-25:

* *IV.5.9 ⟹ IV.5.10*: `(𝒜₁⊗̄ℬ₁) ∩ (𝒜₂⊗̄ℬ₂) = ((𝒜₁'⊗̄ℬ₁') ∪ (𝒜₂'⊗̄ℬ₂'))'`; the
  generated algebra contains every `𝒜ᵢ'⊗1` and `1⊗ℬⱼ'`, hence equals
  `W*(𝒜₁'∪𝒜₂') ⊗̄ W*(ℬ₁'∪ℬ₂') = (𝒜₁∩𝒜₂)' ⊗̄ (ℬ₁∩ℬ₂)'`; one more commutant
  finishes.
* *IV.5.10 ⟹ IV.5.9*: instantiate at `𝒜₁ = M`, `ℬ₁ = B(𝒦)`, `𝒜₂ = B(ℋ)`,
  `ℬ₂ = N`, using only the elementary amplification case.

## 2. Every escape route is closed, and closed by proof

**A special case will not do.** The only instance the thesis ever uses is
`proc.tex:4938`, `Ã⊗𝒞 = (Ã⊗B(ℋ)) ∩ (𝒜⊗𝒞)`. That looks like a special case
(`ℬ₁ = ⊤`, `𝒜₁ ⊆ 𝒜₂`) but is a *presentation* of the general theorem: 125IV
quantifies over all `𝒜`, so taking `𝒜 = B(𝒦)`, `𝒟 = M ⊗̄ 𝒞` and `h` the
inclusion makes `r_ξ(m⊗c) = ⟨ξ,cξ⟩·m`, hence the generated `Ã` exactly `M`.
**Every instance of the general theorem arises as one of 125IV's.**

**The direction used is the hard one.** `proc.tex:4938` uses
`(Ã⊗B(ℋ)) ∩ (𝒜⊗𝒞) ⊆ Ã⊗𝒞`. The `⊇` inclusion — a generator check, the
`sInf_le` idiom used throughout `haTensorPreimage` — is elementary and is never
what a consumer needs.

**The atomic case is already built and cannot reach these statements.** For
hereditarily atomic `𝒜` the slice-map property is *proved*: `haMem`
(`QuantumLambda.lean:3705`), `haE_of_mem` (:3759), on the matrix-unit slice
`haE` (:3398); from them `haTensorPreimage` (:3811) is 125VIIb and
`haTensorBSurj` (:4554) is the hard half of 125eIII. But the algebra that would
have to be atomic is the **tensored** factor, and all seven statements are
general in exactly that slot. Restricting it is 125dII, a different and
already-proved theorem (`ha_tensor_closed`, :4282).

**Slice maps are a dead end, provably.** The Fubini product
`F(M,N) = {x : (ω⊗id)(x) ∈ N, (id⊗ψ)(x) ∈ M}` satisfies `F(M,N) ⊆ (M'⊗̄N')'` by
an elementary computation and `(M⊗̄N)' ⊆ F(M',N')` in three lines — so
Tomiyama's slice-map theorem and the commutation theorem imply each other.
Tomiyama's own paper (*On the tensor products of von Neumann algebras*, Pacific
J. Math. **30** (1969) 263–270, footnote 1 p. 266) says so explicitly and cites
Tomita for the theorem. Slice maps buy the easy half free and nothing else.

**88VI is not the obstruction.** `double_commutant`
(`A/VN/NormalFunctionals.lean:1740`) holds for an arbitrary unital
∗-subalgebra of any `B(H)` — which is exactly the ambient the commutation
theorem lives in, `B(ℋ⊗𝒦)`. The "only for `B(H)`" caveat recorded at
`Projections.lean:4417` is a *different* gap: the relative bicommutant inside an
abstract algebra. It blocks 64II/65IV, not this.

**`intersection_tensor` has no Lean consumer.** `grep concreteTensor` returns
three hits, all inside its own definition and statement. The "blocked on" edges
in `why-open.csv` are route claims about the *printed* proofs. Closing 121II
would additionally require the concrete↔abstract bridge (§5).

## 3. What exists, and what does not

**Mathlib supplies the vocabulary and almost none of the theory** — roughly
10–15%, all definitional. `VonNeumannAlgebra H` is a bicommutant-closed bundled
`StarSubalgebra` with ~15 lemmas, and is an **isolated leaf**: no other file
mentions it, it has no instances (not even for `B(H)`), and it has **no lattice
structure** — `⊤` and `⊓` are advertised in its own docstring but do not exist,
so our target's `∩` is unwriteable in Mathlib's types. The double commutant
theorem is absent in every generality, as are Kaplansky density, the *completed*
tensor product `H ⊗̄ K`, the ultraweak topology, any predual or trace-class
ideal, states, normal maps, cyclic/separating vectors, and the whole of modular
theory.

**Correction, 2026-08-25.** An earlier draft of this file said Mathlib has no
`IsClosable` and no unbounded-operator layer. That is wrong, and the error was
in our favour. `Mathlib/Topology/Algebra/Module/LinearPMap.lean` has
`LinearPMap.IsClosable`, `IsClosable.existsUnique`, `LinearPMap.closure` and
`IsClosable.graph_closure_eq_closure_graph`; `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`
has `IsFormalAdjoint`, `adjointDomain`, `adjoint` (`T†`),
`LinearPMap.IsSelfAdjoint` and `IsSelfAdjoint.isClosed`. What Mathlib lacks is
the *spectral* layer — Borel functional calculus, PVMs, Stone's theorem, polar
decomposition of closed operators — not the bookkeeping. Verified by reading
the sources.

Also relevant and previously under-rated:
`Mathlib/Analysis/InnerProductSpace/StandardSubspace.lean` (Tanimoto, 2026)
supplies the `InnerProductSpace ℝ` structure obtained by restricting a complex
inner product to its real part, `ClosedSubmodule ℝ H`, `mulI` and symplectic
complements — i.e. exactly RvD's §2–3 scaffolding. Its own TODO is "define the
Tomita conjugation, prove Tomita's theorem", so anything built here is
upstreamable.

What Mathlib does have and we would use: `Set.centralizer` with a full algebraic
API and `Set.isClosed_centralizer`; WOT as `E →WOT[𝕜] F` with `Ring`,
`StarRing`, `ContinuousStar`, `IsSemitopologicalRing`; the *algebraic* inner
tensor product with `mapL`/`lTensor`/`rTensor` and their adjoints; `cfc`;
Banach–Alaoglu; Cauchy–Goursat for rectangles; the identity theorem.

**The tree is unusually complete below the theorem.** Present and general:
`double_commutant` (88VI); `commutant_basic_1/2/3'`; intrinsic
ultraweak/ultrastrong topologies with `functional_permanence_2/3` proving the
subalgebra topology *is* the induced one; normality ↔ continuity; **Kaplansky
density** (74IV); uw/us completeness and ball compactness; `exists_cyclic_projection`
(`NormalFunctionals.lean:1212`) — the classical `[Sx] ∈ S'` device, for any
∗-subalgebra of `B(H)`; `hilb_tensor_basic_2` (the ONB `{e⊗f}`); the full
`opTensor` calculus; `special_tensor` + `tensor_uniqueness` (the concrete↔abstract
bridge, in pieces); `normal_functional`; `exists_faithful_normal_rep`;
`gns_normal` with a genuine cyclic vector; `Corner A e` for arbitrary
projections.

Absent from the tree: **any faithful normal state on a non-commutative von
Neumann algebra**, hence no cyclic-*and*-separating vector; σ-finiteness;
modular theory (`grep -i 'tomita\|modular'` over `Theses/` returns nothing);
relative double commutant; `(eMe)' = eM'e`; slice maps in general; and any API
at all for `concreteTensor`.

**`B/Dils`'s self-dual machinery is not a shortcut.** `ba_ext_tensor_iso`
(165VI) is about adjointable operators on an *exterior* module tensor product,
not commutants inside a fixed `B(H)`; at `𝒜 = ℬ = ℂ` it degenerates to
`B(H) ⊗̄ B(K) ≅ B(H⊗K)`, the trivial case. The module-theoretic route to a
commutant is Rieffel induction via the **interior** tensor product `X ⊗_ℬ H`,
which does not exist in the tree and would be a project of the same order.

The one thing worth harvesting from `B/Dils` is not module theory at all:
`Stinespring.lean` has the **ket/slice operator API** that `A/Proc` lacks —
`hilbTensorKet` (:1203), `hilbTensorKet_adjoint_mk` (:1213),
`conjOperator_ketAdjoint` (:1326) — built for a *different* Hilbert tensor
product, transportable along `hilb_tensor_unique` (`Tensor.lean:881`).

## 4. The route, if we take it

**Not** classical Tomita–Takesaki: that needs closed unbounded operators, their
polar decomposition, the spectral theorem, and product spectral measures — a
Mathlib-scale project before one touches modular theory.

**Not** the semifinite/Hilbert-algebra route: it cannot reach type III, and the
only bridge is Takesaki's structure theorem, itself built on modular theory.

**Rieffel–van Daele**, *A bounded operator approach to Tomita–Takesaki theory*,
Pacific J. Math. **69** (1977) 187–221 (open access, msp.org). Proves
`JMJ = M'` with **no unbounded operators anywhere**: `J` and `Δ^{it}` are built
from the two projections onto `closure(M_sa ω)` and its `i`-rotate.

Only the *conjugation* half `JMJ = M'` is needed. Not needed: the modular
automorphism group as a theory, KMS, weights, left Hilbert algebras, the
standard form, Connes cocycles. Cyclic and separating vectors are not assumed —
they are manufactured by an elementary amplify-and-cut reduction (Zorn for
σ-finite corners; `[M'ξ]` has central carrier 1).

| piece | lines |
|---|---|
| unbounded scaffolding (closed operators, adjoints, `ran(T±i)` criterion, uniqueness of polar decomposition) | 600–1200 |
| RvD §2 — `P,Q,R,T,J`, Prop. 2.2 | 500–900 |
| `R^{it}` for injective positive bounded `R` (avoidable without Borel calculus) | 250–450 |
| RvD §3 to Prop. 3.7 | 700–1200 |
| RvD §4, Lemmas 4.3–4.9 and Thm 4.2 — the analytic core | 1500–2500 |
| RvD appendix: identify `S_ω` with `J·b a^{-1}` | 300–600 |
| tensor factorisation `J_ξ = J_ω ⊗ J_{ω'}` | 600–1000 |
| the reduction to the cyclic-separating case | 1500–2500 |
| amplification theorem, `B(L₁)⊗̄B(L₂) = B(L₁⊗L₂)`, flip/associator transport | 800–1500 |
| IV.5.10 from IV.5.9, plus the concrete↔abstract bridge | 400–800 |
| **total** | **≈ 7 000 – 12 000** |

Two to four months. About a third is the RvD analytic core, a third the
reduction and the tensor plumbing, a third an unbounded-operator layer Mathlib
does not have.

### The step that decides it — checked, and the verdict is mixed-but-good

The step `J_ξ = J_ω ⊗ J_{ω'}` classically needs the spectral theorem for
unbounded operators and product spectral measures — the single place the bounded
strategy could fail. A bounded substitute was proposed on 2026-08-25 **and is
flagged as a reconstruction, not a citation**:

> With `a := (R/2)^{1/2}`, `b := ((2−R)/2)^{1/2}` — commuting positive
> injective, `a²+b² = 1`, `Δ^{1/2} = b a^{-1}` on `ran a` — the operator
> `T₀ := Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2}` on `ran(a) ⊙ ran(a')` satisfies
> `(T₀ ± i)(aζ ⊗ a'ζ') = (b⊗b' ± i·a⊗a')(ζ⊗ζ')`, so `ran(T₀±i)` is dense once
> `ker(b⊗b' ∓ i·a⊗a') = 0`; and
> `(b⊗b' ∓ i a⊗a')^*(b⊗b' ∓ i a⊗a') = (b⊗b')² + (a⊗a')² ≥ (a⊗a')²`, injective
> because a tensor product of injective bounded operators is injective. Hence
> `closure(T₀)` is self-adjoint, and uniqueness of polar decomposition gives the
> factorisation.

**Two independent checks, 2026-08-25 — one instructed to refute it, one to
derive the result from scratch and only then compare. They agree, and the
outcome is better than the argument as written.**

*What survives.* The RvD conventions are exactly right — `Δ = (2−R)R⁻¹` is
verbatim from the paper (§2 p. 190, Appendix Prop. 3), confirmed independently
by hand in `M₂(ℂ)` and numerically. `T₀` is well defined and symmetric; the `±i`
identity holds; the density step is right (`ran(T₀±i)` is the image of the
*dense* `ℋ ⊙ ℋ'`, not of `ran(a) ⊙ ran(a')`); the cross terms genuinely cancel
because `a,b` are CFC of the same `R`. And the step flagged in advance as most
suspect — **injectivity of `a ⊗ a'` on the completed tensor product — is simply
true**: expand along an ONB of `ℋ'`, `a⊗1` acts coordinatewise on `⊕_j ℋ`, and
`a⊗a' = (a⊗1)(1⊗a')`. One verifier attacked it specifically and could not break
it.

*What is missing.* Essential self-adjointness of `T₀` is a statement about `T₀`
alone and never touches `(M ⊗̄ N, ξ)`. Two gaps:

1. **Positivity, not just self-adjointness.** Polar uniqueness gives `J_ξ = U`
   only if the positive factor is positive; self-adjoint alone yields
   `J_ξ = U·sgn(C)`. One line — `⟨T₀(Av), Av⟩ = ⟨ABv, v⟩ ≥ 0` — but assumed.
2. **The core property.** Running polar decomposition on `S_ξ` needs
   `dom(T₀)` to be a **core** for `S_ξ`, which essential self-adjointness does
   not supply. The tempting repair is circular: unwinding `Δ_ξ^{1/2} = J_ξ S_ξ`
   shows `T₀ ⊆ Δ_ξ^{1/2}` is *equivalent to* `J_ξ = J_ω ⊗ J_{ω'}` on `ran(T₀)`,
   which is the conclusion.

*Both gaps are fillable with bounded operators*, and the independent
reconstruction did it, with a route better suited to Lean than the original:

* **Normalisation lemma.** For commuting positive injective `c,d` (here
  `c = a⊗a'`, `d = b⊗b'`, where `c²+d² ≠ 1` — which is exactly why `T₀` is not
  already closed), put `h := (c²+d²)^{1/2}`; then `hζ ↦ cζ` and `hζ ↦ dζ` are
  contractive on the dense `ran h` and extend to `c̃, d̃` forming a *modular
  pair*. This **exhibits the closure explicitly**, so self-adjointness needs no
  deficiency-index criterion — and the isometry `η ↦ (c̃η, d̃η)` onto the graph
  gives the core property for free: `c(E)` is a core for every dense `E`.
* **Polar uniqueness, bounded.** `(1 + D²)⁻¹ = a²` as an everywhere-defined
  bounded operator, so `D₁² = D₂² ⟹ a₁ = a₂ ⟹ D₁ = D₂` by uniqueness of the
  *bounded* positive square root. This is what replaces uniqueness of unbounded
  positive square roots.
* **No antilinear tensor product is needed.** Instead of building
  `J_ω ⊗ J_{ω'}` as an antilinear operator (a real Lean trap — the map is
  ℝ-bilinear, not ℂ-bilinear, so it does not factor through `ℋ ⊗_ℂ ℋ'`), define
  the ℂ-linear unitary `W(ζ⊗ζ') := J_ξ(J_ω ζ ⊗ J_{ω'} ζ')`, which *is*
  ℂ-bilinear because two conjugations compose. The conclusion `W = 1` is the
  factorisation.
* The one place von Neumann algebra theory enters is **Kaplansky density**, to
  show `span(Mω ⊙ Nω')` is a core for `S_ξ` — and the self-adjoint version
  suffices, splitting `z = z₁ + iz₂`, which the tree already has as
  `kaplansky_sa` (`A/VN/Completeness.lean:2631`).

The whole chain — including the non-obvious
`R_ξ/2 = c²(c²+d²)⁻¹` — was verified numerically to machine precision
(2e-14) on `M₂ ⊗ M₃` with random densities, building `𝒦`, `P`, `Q`, `R` from
scratch in the real Hilbert space.

*The honest correction to the cost.* "Bounded operators only" is **not** what
this buys. You still need closed densely defined operators, cores, adjoints and
polar uniqueness — Mathlib has the bookkeeping for all of these (see §3). What
RvD buys is that **`Δ^{1/2}` never needs a spectral measure**: it is `b a⁻¹` for
bounded `a,b`. That is the real saving, and it stands.

*And the cost re-weights.* The tensor step is **not** the expensive part —
estimated 800–1500 lines given the tree's `HT`/`opTensor`/Kaplansky. The bulk is
the RvD single-algebra package: `𝒦 = closure(M_sa ω)` standard, the real
projections `P,Q`, `R = P+Q` complex-linear and positive with `R, 2−R`
injective, `J := (P−Q)T⁻¹` by continuous extension, and `Mω` a core.

**CORRECTION, 2026-08-26 — this paragraph used to end by claiming the
conjugation half needs "not `Δ^{it}`, and therefore not the Borel functional
calculus RvD use for `R^{it}`". That is wrong, and it was the central cost
claim of this document.** The worker who read RvD §§3–4 in full traced the
dependency: Lemma 4.9 proves `JMJ ⊆ M'` by pure algebra, but it *consumes*
`JM'J ⊆ M`, which is **Lemma 4.8 at `t = 0`** — and 4.8's proof runs the whole
one-parameter group, showing `g(t) = ⟨[y', Δ^{it}Jx'JΔ^{-it}]ξ, η⟩` satisfies
`∫ e^{-φt}(2cosh πt)^{-1} g(t) dt = 0` for all `φ ∈ (−π,π)` and concluding
`g ≡ 0` by the identity theorem plus Fourier injectivity. **`g(0) = 0` alone is
not obtainable.** There is no algebraic shortcut: solving Lemma 4.5's
`Δ^{1/2} y Δ^{1/2} = λΔx + λ̄xΔ` for `y` is inverting `2cosh(s + iφ/2)` where
`e^{2ist}` is the modular flow — inherently a Fourier inversion.

So `Δ^{it}` is needed. **But the Borel functional calculus still is not**, and
that is what saves the route: for `Im z ≤ 0` the function `t ↦ t^{1+iz}` is
continuous and bounded on `[0,2]`, so `cfc` gives `R^{1+iz}`; the pointwise
bound `|t^{1+iz}|² ≤ 2^{-2Im z}·t²` gives `‖R^{1+iz}ζ‖ ≤ 2^{-Im z}‖Rζ‖` by cfc
monotonicity; and `Rζ ↦ R^{1+iz}ζ` extends off the dense `ran R` by
`LinearMap.extendOfNorm` — the same device already used for `J` and for the
normalisation lemma. Holomorphy in `z` follows because `z ↦ (t ↦ t^{1+iz})` is
a holomorphic `C([0,2])`-valued map and `cfcHom` is an isometric algebra map.
That is Lemma 3.6 entire, ≈400–700 lines.

What *is* skippable, confirmed by reading: all of §3 except Lemma 3.6 (Def. 3.4
and Props 3.3/3.5/3.7 and Thms 3.8/3.9 are KMS), Thm 4.10, and all of §5.

*Still worth obtaining.* Rieffel & van Daele, Bull. LMS **7** (1975) 257–260 —
reference [10] of the 1977 paper, and about precisely this theorem. Both
verifiers hit paywalls. It predates the bounded reformulation and may sidestep
the factorisation step entirely.

## 5. Worth building either way

These are consumed by every route and have value on their own:

1. ~~**The amplification theorem**~~ — **DONE**, `982d7f8`. See §6.
2. ~~**`concreteTensor`'s API and the concrete↔abstract bridge**~~ — **DONE**,
   see §6. The "and even then it would not connect" objection is gone.
3. ~~**One factor atomic type I**, `N ≅ ⊕_j B(𝒦_j)`~~ — **DONE**. See §6.
4. **Both algebras finite with cyclic trace vectors**: here `J` is *bounded*
   (`‖x*ω‖² = τ(xx*) = τ(x*x) = ‖xω‖²`), `JMJ = M'` is the Murray–von Neumann
   argument, and `J_{ω⊗ω'} = J_ω ⊗ J_{ω'}` is immediate — two bounded
   conjugations agreeing on a total set. A genuine, if restricted, commutation
   theorem for ~800–1200 lines.

None of 1–4 closes any of the seven as stated. 3 widened the atomic branch, and
is done.

## 5a. Progress against the estimate

*Updated 2026-08-26. Estimates are §4's; actuals are committed, `sorry`-free and
axiom-clean in situ.*

| piece | estimate | actual | commit |
|---|---|---|---|
| RvD §2 — `P,Q,R,T,J`, Prop. 2.2 | 500–900 | **683** | `fa6de2c` |
| the bounded core (modular pairs, Lemmas A–D) | part of the 600–1200 scaffolding row | **828** | `5819fac` |
| RvD Prop. 4.1 + the von Neumann bridge | not separately costed | **716** | `5ba287a` |
| the reduction — steps 0–3, cutting, cancellation | 1500–2500 (revised to 3500–5200) | **1233** | `5ba287a` |
| the corner Hilbert space and corner tensor | 1200–2000 (the revision's critical path) | **772** | `93287f6` |
| amplification theorem + ket/slice API | in the 800–1500 row | **306** | `982d7f8` |
| `concreteTensor` API + concrete↔abstract bridge | 400–800 | **616** | `affa026` |
| atomic type I widening of `haE` (§5 item 3) | 400–700 | **1199** | `a992c23` |
| RvD Prop. 4.1 → Thm 4.2, conditional on Lemma 4.8 | part of the 1500–2500 §4 row | **1240** | `71cfef0` |
| the tensor factorisation `J_ξ = J_ω ⊗ J_{ω'}` | 600–1000 | **1242** | `5d816fc` |
| flip, associator, `B(L₁)⊗̄B(L₂)`, unitary transport | 800–1500 (with amplification) | **925** | `54859e6` |
| the reduction's sharp limit (`CT_of_CT_finCyclic`) | — | **383** | `8dd8f97` |
| `Δ^{it}` — RvD Lemma 3.6 and the modular group | 250–450 + 700–1200 | **1048** | `22767bd` |
| RvD Lemmas 4.5 and 4.6 | 300–500 + 400–700 | **1138** | `6a0cc8d` |
| RvD Lemma 4.8 and the Laplace layer | 300–500 | **731** | `0ebe52b` |
| RvD Lemma 3.6 (analyticity) + Lemma 4.7 | 250–350 (a,b only) | **1179** | `?` |
| **total so far** | | **≈ 14 200** | |

**`J M J = M'` is proved, unconditionally** (`tomita_JMJ_unconditional`), for a
von Neumann algebra with a cyclic and separating vector. That is Tomita's
theorem, the conjugation half — the piece this whole route was built to reach,
and the one the literature says needs modular theory. It needs no Borel
functional calculus, no projection-valued measure, and no spectral theorem for
unbounded operators anywhere in its dependency cone.

**Open, as of 2026-08-26, and it is one statement:** *the compression of a von
Neumann algebra is a von Neumann algebra* — `(f𝒯f)□ = 𝒯□f` for `f ∈ 𝒯`, i.e.
normality of `w ↦ PwP*`. `CornerTensor.lean` deliberately avoided it and the
tree does not have it. The classical proof extends `y ∈ (f𝒯f)□` to
`ŷ(x f ζ) := x ỹ f ζ` on the dense `𝒯fℋ`; well-definedness and boundedness are
the content.

Everything else is done. Tomita's theorem is proved unconditionally; the
reduction runs from the general case down to **algebras with a cyclic vector**
(`CT_of_CT_cyclic`); and the one remaining step is from *cyclic* to
*cyclic-and-separating*, which needs exactly the statement above.

**Why that last step is not optional, proved two ways (2026-08-26).** The plan
said the `ℂⁿ` amplification carries `CT_of_CT_finCyclic` to the
cyclic-and-separating case. It does not.
* **Amplification never manufactures a separating vector.** Take `𝒜 = B(ℋ)`
  with `dim ℋ = ∞`: every nonzero vector is cyclic, so `HasFinCyclic` holds,
  and `𝒜 ⊗̄ B(ℒ) = B(ℋ⊗ℒ)`, which has a separating vector only if `dim ≤ 1`.
* **Nor can the cutting machinery reach it, in any orientation.** The cuts
  `CT_of_relCT` admits are `e ∈ 𝒜□`, and `𝒜_e` has a cyclic *and* separating
  vector iff `[𝒜ξ] = e = [𝒜□ξ]` — the first forces `e ∈ 𝒜□`, the second
  `e ∈ 𝒜`, so `e ∈ Z(𝒜)`. For a factor with no separating vector the only
  central cuts are `0` and `1`.

This sharpens the retraction below: it is not merely that the cyclic family
fails to be directed, it is that **the target class is unreachable by cutting.**
What the amplification *does* buy is essential — cyclicity of `ξ` makes the
carrier `f = [(𝒜□⊗1)ξ]` have central carrier `1`, so a single non-directed cut
suffices in principle — but `f` lies **in the algebra**, not the commutant, and
transporting `CT` across a cut inside the algebra is exactly the hard half of
the reduction theorem.

**The holomorphy question, settled 2026-08-26 — and the answer corrects what
was recorded here yesterday.** `ModularGroup.lean` left holomorphy out and
recorded a claim that Lemma 4.8 does not need it. *That claim is true.* Lemma
4.8's identity-theorem step is holomorphy in the **Fourier parameter**, by
dominated convergence, with no operator-valued holomorphy anywhere — now proved
outright as `differentiableAt_lapl`. **But the conclusion drawn from it, that
the conjugation half therefore needs no holomorphy of `R^{iz}`, is false.**
Lemma 4.8's first line consumes **Lemma 4.7**, and 4.7 (RvD p. 204) applies
Lemma 4.6 to
`f(z) = ⟪R^{-z+1/2}(2−R)^{z+1/2} x R^{z+1/2}(2−R)^{-z+1/2} ξ, η⟫` on
`|Re z| ≤ 1/2`, justified by the single sentence *"from Lemma 3.6 it follows
that `f` satisfies the requirements of Lemma 4.6"* — i.e. precisely Lemma 3.6's
continuity and analyticity clauses. **So `R^{iz}` holomorphy is on the critical
path, consumed by 4.7 rather than by 4.8.**

Two findings that re-cost it downward:

* **Inside the open strip nothing but `cfc` is needed.** For `|Re z| < 1/2` all
  four exponents `±z+1/2` have real part strictly in `(0,1)`, so every factor is
  plain `cpowOp = cfc (·^w)`. `DifferentiableOn ℂ f opStrip` reduces to
  `HasDerivAt (fun w ↦ cfc (·^w) X) (cfc (fun u ↦ u^w log u) X) w` for
  `Re w > 0`, via `norm_cfc_le` and the scalar estimate `t^c(log t)² ≤ 4/c²`.
  The `extendOfNorm` device is needed only on the **boundary** `Re z = ±1/2`,
  and there only for *continuity*; boundedness is free, since `|t^w| ≤ 2` on
  `[0,2]`.
* **A convention trap.** Mathlib's inner product is conjugate-linear in the
  first slot, so `z ↦ ⟪A(z)ξ, η⟫` is *anti*holomorphic. The function handed to
  `lemma_4_6` must be `f z = ⟪η, A(z) ξ⟫`.

One instance of the theorem is already proved outright: `CT_top_right`
(`54859e6`), the amplification case `(𝒜 ⊗̄ B(𝒦))□ = 𝒜□ ⊗̄ ℂ1`.
*(Status report of 2026-08-25, not a dependency: `commutation_theorem` is now
unconditional and subsumes `CT_top_right`, which is a consumer-free special
case — `docs/DEAD-LIMBS.md` §10c.  Its two siblings `CT_top_left` and
`CT_top_top` were deleted on 2026-08-27, §12b; `CT_top_right` was kept, on the
strength of this sentence and of the module docstring of
`A/Proc/TensorTransport.lean`.  The term-level cone pass of 2026-08-27
(§13.5 of `DEAD-LIMBS.md`) then placed `CT_top_right` outside the cone too,
along with both of the consumers that §10c had counted for it, so the keep
rests on the record the statement makes and not on a consumer.)*

**What the actuals say about the estimate.** Four of the eight rows came in at
or below the low end, one (the reduction's own critical path) at 60% of it, and
one — the atomic type I widening — at 1.7× the high end. The single largest
correction was not a line-count error at all but a *structural* one: the
reduction's expensive step was thought to be transport of von Neumann algebras
onto the corner, and it turned out that step is not needed (see §6).

**Every worker so far has found at least one place where the brief named the
wrong hard step.** That is now the expected outcome of a round rather than a
surprise, and it is why each of these was scoped by a worker with licence to
contradict the plan rather than handed down as a specification.

## 6. Already banked

**Atomic type I is banked** (§5 item 3). The `haE` device now runs on
`𝒜 ≅ ⊕_j B(𝒦_j)` with the `𝒦_j` *arbitrary* nonzero Hilbert spaces, not only
on `⊕_j M_{n_j}`: `AtomicTypeIRep`/`AtomicTypeI` (the sibling of 84bII
`HereditarilyAtomic` that the tree did not have), the widened slice `atE`,
both halves of the slice-map property (`atMem`, `atE_of_mem`), and two public
consequences — `atomicTypeI_tensor_preimage`, which is **125VIIb** for atomic
type I `𝒜`, and `atomicTypeI_tensorBsurjectivity`, which is **125eIII** for
atomic type I `ℬ` in **both** directions, hence the atomic type I case of the
`←` half that is still `sorry` in general. ~1200 lines in
`A/Proc/QuantumLambda.lean`, no statement changed, axiom-clean in situ.

*The only new mathematics is the convergence step, and it is cheap.* Finite
dimensionally `∑_p u_{pp} = 1` on the nose, so the block expansion
`z_j x = ∑_{k,l} E_{kl}(x)(1 ⊗ u_{kl})` is a finite identity and the only limit
taken is the one over `Finset J` (`haApprox`). For `dim 𝒦_j = ∞` the partial
sums `p_F = ∑_{p ∈ F} u_{pp}` merely *increase to* `1` — that is Parseval, and
it is `bkP_isLUB` — so the expansion becomes the two-sided compression
`(1 ⊗ p_F)·x·(1 ⊗ p_F) = ∑_{k,l ∈ F} E_{kl}(x)·(1 ⊗ u_{kl})` and the limit has
to be taken *inside a product*. Ultraweak convergence does not survive
multiplication; but for a **monotone net of projections** Cauchy–Schwarz
(43I.1, `norm_apply_star_mul_le`) does it in four lines,
`|ω(zxz − pxp)| ≤ (‖(zx)*‖_ω + ‖x‖·ω(z)^{1/2})·ω(z − p)^{1/2} → 0`
(`uw_compress_tendsto`). No ultrastrong topology, no Kaplansky density, no
joint continuity on bounded sets. So the answer to what §5 item 3 was really
asking — *does the infinite-dimensional case lose the free convergence the
finite one has?* — is: it loses it, and buys it back for four lines.

*What did **not** widen, and why.* 125dII `ha_tensor_closed` and the 125eVII
assembly are **not** widened, because doing so changes statements rather than
proofs. `HaFreeExp` carries `ha : HereditarilyAtomic carrier` as a field *and*
quantifies its universal property over hereditarily atomic `C'`, so the atomic
type I version is a different theorem — the free exponential of the atomic
type I subcategory — and its solution set (`HaSolProd`,
`hereditarilyAtomic_haSolProd`, the 125II cardinality bound) is built out of
the finite matrix combinatorics, with no `B(𝒦)` analogue in the tree. Recorded
as a statement-level item for the author rather than attempted.

*One formal gap worth naming.* `HereditarilyAtomic → AtomicTypeI` is true but
is **not** proved. It needs `M_n ≅ B(ℂ^n)` (Mathlib has
`Matrix.toEuclideanCLM`) plus a universe lift, because
`EuclideanSpace ℂ (Fin n) : Type 0` while `AtomicTypeIRep.K : J → Type u`, and
neither Mathlib nor the tree puts an `InnerProductSpace` structure on `ULift`.
Nothing downstream needs it; it is plumbing, not mathematics, if anyone wants
the containment on the record.


**The amplify-and-cut reduction is complete.** `Commutation.lean` (`5ba287a`,
1233 lines) has steps 0–3, the cutting principle, the reduction theorem
`(M_e)□ = (M□)_e` — 35 lines, stated relative to `pB(ℋ)p` so that "extension by
zero is the identity" does the work — and the cancellation half of step 4.
`CornerTensor.lean` (`93287f6`, 772 lines) has the corner Hilbert space,
`pB(ℋ)p ≅ B(eℋ)` in both directions, the corner reduction theorem, and the
capstone `CT_of_CT_corner`. Together: **the general commutation theorem follows
from the commutation theorem for the corner algebras.**

Three findings from those two rounds that changed the plan rather than merely
executing it:

* ~~**σ-finiteness is not needed anywhere**, and neither is step 3's `ℓ²(ℕ)`
  amplification.~~ **RETRACTED 2026-08-26 — this was wrong, and I propagated it
  into the plan and into three later briefs before it was checked.** The
  amplification is structurally necessary. `CT_of_relCT` and `CT_of_compress`
  consume a **monotone** net of cuts with supremum `1`, so the admissible cuts
  must be *directed* — and for a cut `e ∈ 𝒜□`, the corner `𝒜_e` has `ξ` cyclic
  iff `e = [𝒜ξ]` and separating iff also `e = [𝒜□ξ]`. **Neither family is closed
  under joins.** Two counterexamples pin it: for `𝒜 = ℂ·1 ⊆ B(ℋ)` with
  `dim ℋ ≥ 2` the cuts are all of `B(ℋ)`, but `𝒜_e = ℂe` has a cyclic vector
  only when `dim eℋ = 1`, and rank-one projections do not increase to `1`; for
  `𝒜 = B(ℋ)` the only cut is `e = 1`, and `B(ℋ)` has no separating vector.
  Dualising via `CT_iff_vnComm` swaps the two examples, so **no orientation of
  the cut and no choice of Zorn family works**.  (That dualisation is a *prose*
  argument about the two counterexamples; the Lean `CT_iff_vnComm` was never
  invoked for it, and has no consumer — `docs/DEAD-LIMBS.md` §7.) `exists_separating_corner` does
  give a separating vector — but for a *non-directed* cut, which is exactly what
  the amplification repairs, since `n` jointly cyclic vectors become one after
  tensoring with `ℂⁿ`.
* **The upward transport `(𝒜 ⊗̄ ℬ)_{e⊗f} = 𝒜_e ⊗̄ ℬ_f` is not needed and not
  proved.** Its `⊇` half is normality of `w ↦ PwP*` — a real chunk of work,
  absent from the tree. The reduction only needs `{w | PwP* ∈ 𝒯}` to be a von
  Neumann subalgebra, and by the corner reduction theorem that set is *literally
  a commutant*, hence vN by 65III. This is why the critical path closed in one
  round instead of two.
* **`P = a² + abJ`, hence `𝒦 = a(fix J)`** — the bridge from the real subspace
  to `dom Δ^{1/2}`, which appeared in no plan and without which there is no
  route from `𝒦` to the modular pair at all. It needs `JaJ = b`, proved by
  building `JaJ` as a *complex*-linear operator (it commutes with `i` because
  `J` anticommutes twice).

**RvD's own scaffolding is in.** `Modular.lean` (`5819fac`) — modular pairs,
`D_{a,b}` self-adjoint positive injective, the normalisation lemma exhibiting
the closure explicitly with its core, `(1+D²)⁻¹ = a²`, polar rigidity — and
`StandardSubspace.lean` (`fa6de2c`) — `P`, `Q`, `R` complex-linear positive,
`T`, `J` with `J² = 1` and `JR = (2−R)J`, `A = JT`, and `isModularPair_a_b`
delivering the pair with no glue. `Tomita.lean` (`5ba287a`) joins them to von
Neumann algebras: `𝒦 = closure(M_sa ω)` is standard (cyclic gives `⊔ = ⊤`,
separating gives `⊓ = ⊥`), `dom D = 𝒦 + i𝒦`, `J(D(xω)) = x*ω`, and `Mω` a core
— **all without ever defining `S_ω`**, so no unbounded conjugate-linear operator
appears anywhere in the development.

Two things worth knowing for whoever continues. `IsCommutingPair.hasCore`
delivers a core of the form `a(E)` and **cannot** be used to show `Mω` is a core
for `Δ_ω^{1/2}` — the only candidate `E := a⁻¹(Mω)` has density equivalent to
the conclusion, so it is circular there; the graph-closure argument is reproved
directly at `Tomita.lean:565-644`. And `Measurement.lean`'s `Corner A e` is the
*abstract* corner with no Hilbert space attached, so it does not give
`pB(ℋ)p ≅ B(eℋ)`.

**The concrete↔abstract bridge closes.** `concreteTensor` went from zero
lemmas to a full API — including `concreteTensor_eq_wstar_spatialSpan`, which
hands it everything already proved about `spatialSpan`, and
`concreteTensor_inf_le_inf`, the easy half of 121II free from monotonicity.
On top of it: `concreteTensorEquiv`, the canonical nmiu-isomorphism
`VNSub _ (concreteTensor H K SA SB) ≅ VNT (VNSub _ SA) (VNSub _ SB)` from
`special_tensor` (111VII) fed to `tensor_uniqueness` (114II), sending `a ⊗ b`
to `a ⊗ᵥ b` and unique in doing so; the two-sided `tensorSub₂`; and the
transport itself, `tensorSub_inf_of_intersectionTensorStatement` — **granted
121II, the fully abstract identity `tensorSub 𝒞 S₁ ⊓ tensorSub 𝒞 S₂ =
tensorSub 𝒞 (S₁ ⊓ S₂)` in `VNT 𝒜 𝒞`, with no concreteness assumption on `𝒜`
or `𝒞`** (realised via `ngns_ulift` and transported). 121II is packaged as
`IntersectionTensorStatement`, and a proved 121II is *literally* a proof of it:
the `fun ... => intersection_tensor ...` term typechecks with no glue.
616 insertions, zero deletions, no statement changed, axiom-clean in situ.

**Residual caveat for whoever attacks 125IV**: what is delivered is the
*binary* identity, matching 121II's own statement. If `equaliser_lemma`'s
construction needs intersections of arbitrary or transfinitely indexed
families rather than pairs, the binary form must be iterated, and 121II as
stated does not give the infinitary version directly. Everything else 125IV
needs — the cardinality bound, the construction of `𝒜̃`, the equaliser clause
— is independent of the bridge.

`982d7f8` — **the amplification theorem `(M ⊗ 1)' = M' ⊗̄ B(𝒦)`**, in three
forms, with the ket/slice API for `HT ℋ 𝒦` that the tree lacked. Built
natively, not transported: the API has to live in `A/Proc/Tensor.lean` (the
theorem needs `spatialSpan`/`opTensor`) and `A/Proc` cannot import `B/Dils` —
the dependency runs the other way. The proof avoids orthonormal bases entirely,
using a single unit vector `e` and `x ⊗ y = (1 ⊗ |y⟩⟨e|)(x ⊗ e)` rather than a
matrix over an ONB, so there is no summation or convergence argument at all;
`hilb_tensor_basic_2` is never needed. The degenerate `𝒦 = 0` case is handled
by `ht_subsingleton`. 306 lines, no statement changed, axiom-clean in situ.

`96e34ef` — **125eIII is half proved.** The `mp` direction needs neither the
`(·)⊗ℬ`-surjectivity hypothesis nor atomicity: it is `proc.tex:5620` via
`tmapM_range_le` and 69IVb `nmiu_image`, fifteen lines, machine-checked in full
generality. The remaining `sorry` is exactly `mpr` (`proc.tex:5600`), which
needs 125VIIb. The CSV row had the two directions **inverted** relative to the
Lean iff; corrected.

## Sources

Rieffel & Van Daele, *A bounded operator approach to Tomita–Takesaki theory*,
Pacific J. Math. **69** (1977) 187–221 — full text read. Rieffel & Van Daele,
*The commutation theorem for tensor products of von Neumann algebras*, Bull.
LMS **7** (1975) 257–260 — **abstract only, full text not obtained**; its Thm 1
is quoted in the 1977 paper's Prop. 4.1. Tomiyama, Pacific J. Math. **30**
(1969) 263–270 — full text read. Takesaki, *Theory of Operator Algebras I*,
Thm IV.5.9 / Cor. IV.5.10; *Tomita's Theory of Modular Hilbert Algebras*, LNM
128 (1970). Kadison–Ringrose II, chs. 9 and 11 — chapter titles verified,
theorem numbers not.

---

## 7. The last five, and what closing them corrected

*2026-08-26.  `QuantumLambda.lean` is `sorry`-free.  ~640 lines added, no
statement changed, all five axiom-clean in situ
(`propext`, `Classical.choice`, `Quot.sound`).*

**The file-order problem again.** All five statements had to be **moved to
the end of the file**, after `equaliser_lemma`.  This is the same species of
obstacle as the import cycle that blocked 121II (§1's banner): 125IV sits at
the end of `QuantumLambda.lean` because it needs `tensorSub₂`, and the five
statements that consume it were at their parsec positions two thousand lines
above it.  Nothing between the old and new positions refers to any of the
five, so the move is free; but it is not optional, and a new module
downstream cannot substitute, because the `sorry`s live in this file.

**The one ingredient nobody had costed: the *converse* slice-map property.**
`EqL` had `mem_tensorSub_of_rSlice_mem` — *if every slice `r_ξ(x)` lies in
`𝒮`, then `x ∈ 𝒮 ⊗ B(ℋ)`*.  The other direction — *the slices of an element
of `𝒮 ⊗ B(ℋ)` lie in `𝒮`* — was missing, and three of the five need it.  It
is cheap and needs **no** commutation theorem: `𝒮 ⊗ B(ℋ)` is on the nose the
range of `ι ⊗ id` for the inclusion `ι : 𝒮 ↪ 𝒞` (a von Neumann subalgebra by
69IVb containing the generators), and `r_ξ` is natural, so the slice of
`(ι ⊗ id)(w)` is `ι` of the slice of `w`.  Fifteen lines
(`rSlice_mem_of_mem_tensorSub`).  With both halves in hand the general
125VIIb is `mem_tensorSub_of_image` — that is, 121II — and nothing else.

**Two places where the brief named the wrong hard step.**

* *125eIIa.* The plan said "the `(·)⊗ℬ`-surjectivity half is free; only
  `s(𝒜) ⊆ 𝒞̃⊗ℬ` is hard".  **It is exactly backwards.**  `s(𝒜) ⊆ 𝒞̃⊗ℬ` is
  125IV's own `hmemS` step, already packaged; it is the free half.  The
  surjectivity half is the one with content: it needs `𝒞̃` to be the
  ***least*** von Neumann subalgebra with `s(𝒜) ⊆ 𝒞̃ ⊗ ℬ`, and minimality is
  precisely the converse slice-map property above.  Once you build the least
  one (`exists_minimal_tensorSub` — same generating set `{r_ξ(s(a))}` as
  125IV, plus minimality), 125eIIa is four lines.
* *125VIII.* The plan said `equaliser_lemma` is used "**only** for the
  cardinality clause".  True of the *printed* proof, false of the formal
  one, and the gap is not bookkeeping.  Freyd's GAFT is not in the tree, so
  the free object has to be **constructed**, and the construction needs three
  things, not one: (i) the solution-set condition — that is the cardinality
  clause, 125IV + 124I + `exists_smallRealization`, exactly as costed;
  (ii) distributivity `(⊕ᵢ𝒟ᵢ) ⊗ 𝒜 ≅ ⊕ᵢ(𝒟ᵢ ⊗ 𝒜)`, which is 117III through
  119IVc and which `exists_matSumTensorIso` only had for *matrix* summands
  (the general version is shorter — the `punitSum` universe shuffle was what
  the matrix case needed); and (iii) the **uniqueness** clause of the
  universal property, which is *not* downstream of the cardinality bound at
  all.  Uniqueness holds because the unit is `(·) ⊗ 𝒜`-surjective, which is
  again minimality, which is again the slice-map property, which is again
  121II.  So 125VIII consumes 125VIIb-grade machinery and not merely 125IV.

**And one step the plan did not mention at all: equaliser maps are
injective.** `proc.tex:4990` gets uniqueness in 125VI from 114I
`tensor-injective` applied to `e`, having said in passing that "the equaliser
map `e` is injective".  In Lean `IsNMIUEqualizer` is an abstract universal
property, from which one gets that `e` is **monic**, not injective, and the
two are not the same thing a priori.  The repair is to compare with the
concrete equaliser 47V `vn_equalisers` builds — a von Neumann subalgebra of
`𝒜` with the inclusion for its map: `e` corestricts to it, the two universal
properties make the corestriction a two-sided inverse of the comparison map,
and `e` is then a composite of two injections (`nmiuEqualizer_injective`).
Thirty lines, and without them 125VI does not close.

**What is reusable.** `rSlice_mem_of_mem_tensorSub` (the converse slice-map
property), `tensorSub_map_left` / `tensorSub_map_right` (functoriality of
`𝒮 ⊗ 𝒜` in either factor), `exists_minimal_tensorSub` and
`tensorBSurjective_of_minimal` (the least `𝒮`, and why least is 125eII's
notion of surjectivity), `nmiu_ext_of_tensorBSurjective` (a
`(·) ⊗ 𝒜`-surjective map is epi after `⊗ 𝒜` — the uniqueness engine of
125VIII), `exists_sumTensorIso` (117III for arbitrary summands) and
`nmiuEqualizer_injective`.  All at the end of `QuantumLambda.lean`.
