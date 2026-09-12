# Operator-algebraic analysis and reconstruction in effectus terms — research note (2026-09-12)

No Lean. Sources read: eff.tex 208III (`diamond-oml`), 211II (`&`-effectus), 215I/215III
(†-effectus, `dagger-theorem`), 220II (dilations), 225IV–VIII (SEA, Gudder–Latrémolière);
proc.tex 105V (`positive-map-uniqueness`), 106I/106III (sequential-product axioms A–E);
dils.tex 146VII (ultranorm), 149V (`dils-selfdual`), 150II (`dils-completion`);
vn.tex ch. 2 (carriers) and 5 (hereditarily atomic). Errata context: 106III.3 clause (E)
refuted in `B(ℂ²)` (docs/DECISIONS.md 1.6). Four topics, each with a first statement,
plausibility, refutation risk, sketch. "Thm" = argued below; "Conj" = evidence only.

## 0. One observation that shapes everything

`𝒜` and its opposite algebra `𝒜ᵒᵖ` have the same effects, the same projections and the
same sequential product: `√a ·ᵒᵖ b ·ᵒᵖ √a = √a b √a`. So `(Pred, ⊑, ⊥, &, sharp)` of an object
of `vNᵒᵖ` cannot distinguish `𝒜` from `𝒜ᵒᵖ`, and Connes' type III factor that is not
anti-isomorphic to itself shows the two are genuinely different objects of `vNᵒᵖ`
(`Hom` differs: `id : 𝒜 → 𝒜` is not cp as a map `𝒜ᵒᵖ → 𝒜`). Consequences:
* any reconstruction from predicate data alone lands at best in Jordan (`JBW`/`EJA`), exactly
  as in Alfsen–Shultz, where `𝒜 ↦ 𝒜_sa` forgets the orientation; recovering `vN` needs the
  *maps* (cp-ness), e.g. the tensor product of proc.tex §111–119, or an orientation datum;
* `&` is "Jordan-blind", which is why (iii) below works uniformly for `vNᵒᵖ` and `EJAᵒᵖ`.

## (i) Reconstruction: `†`-effectus ⟹ Jordan, plus tensors ⟹ `vN`

Closest known result: Alfsen–Shultz, *Geometry of state spaces* (2003), chs. 8–10 — a spectral
duality `(A, V)` (order-unit space with base-normed predual) whose compressions satisfy the
"standing hypotheses" plus the Hilbert-ball / symmetry-of-transition-probabilities axioms is a
`JBW`-algebra; a `JBW`-algebra is `𝒜_sa` for a von Neumann algebra iff it carries a *dynamical
correspondence* (Alfsen–Shultz 1998, orientation). Solèr/Piron only reach type I (`B(H)`,
atomistic lattice with covering law); Barnum–Müller–Ududec and Wilce are finite-dimensional.
So the target theorem is Alfsen–Shultz with their compressions replaced by `asrt_s`.

**Lemma R1 (first lemma; Thm modulo eff.tex lemmas).** In an `&`-effectus with `s` sharp,
`asrt_s` is an Alfsen–Shultz compression on `Pred X`: (a) `asrt_s ∘ asrt_s = asrt_s`
(`s & s = s`); (b) `1 ∘ asrt_s = s`; (c) `p ∘ asrt_s = p ⟺ p ≤ s` and `p ∘ asrt_s = 0 ⟺ p ≤ s⊥`
(from `⌈p ∘ asrt_s⌉ = ⌈p⌉ ∧ s`-type facts of ⋄-effectuses); (d) `asrt_{s⊥}` is the complement:
`asrt_s ∘ asrt_{s⊥} = 0` and a state `ω` with `s ∘ ω = 1` satisfies `asrt_s ∘ ω = ω`
(`ω` factors through the comprehension `π_s`, and `asrt_s ∘ π_s = π_s`). Risk: low; (c) is a
paraphrase of `s & p = p ⟺ p ≤ s`, which for `vNᵒᵖ` is `sps = p ⟺ ⌈p⌉ ≤ s`.

**Conj R2 (Jordan reconstruction).** Let `C` be a `†`-effectus with scalars `Pred 1 ≅ [0,1]`
whose predicate effect modules are *normal*: `Pred X` has bounded directed suprema and
`Stat X` separates it, and *spectral*: every `p ∈ Pred X` is a norm-limit of `⊕ λᵢ sᵢ` with
`sᵢ` pairwise orthogonal sharp. Then `X ↦ (span Pred X, Jordan product from &)` is a
full and faithful functor `C → JBWᵒᵖ` (`JBW`-algebras, normal positive unital maps), with
`a ∘ b := ½((a ⊕ b)² − a² − b²)` on effects (polarisation of `p ↦ p & p`). Evidence: R1 gives
the compressions; spectrality is Alfsen–Shultz's "spectral duality"; the square-root axiom
215III.1 gives `√·`, and 215III.2 (`asrt²_{p&q} = asrt_p ∘ asrt²_q ∘ asrt_p`) is the fundamental
formula `U_{U_p q} = U_p U_q U_p` of quadratic Jordan algebras (eff.tex 215VII already says so).
What is *missing* from the effectus axioms is Alfsen–Shultz's symmetry of transition
probabilities (for atoms `s, t` with `s & t = λ_{st}·s`: `λ_{st} = λ_{ts}`). The dagger gives
`asrt_s asrt_t asrt_s = asrt²_{s&t} = λ_{st} asrt_s` and the mirror identity, but pairing the two
scalars needs a trace-like state. **Refutation risk: medium** — the honest form of R2 may need
symmetry of transition probabilities as an extra axiom, and in the non-atomic (type II/III)
case Alfsen–Shultz replace it by the "ellipticity" of `Stat X`, which has no effectus phrasing
yet. First test: does a `†`-effectus structure on `Pred = [0,1]`-valued functions on a
*non-symmetric* spectral convex set (Alfsen–Shultz 1976 Memoir examples) exist? If yes, R2 is
false as stated and symmetry must be added.

**Conj R3 (from Jordan to vN).** If moreover `C` is monoidal with the universal property of
proc.tex §113 (the tensor classifies "bi-maps" `X × Y → Z` with sharp-commuting marginals) and
the tensor of `†`-unitaries is `†`-unitary, then the image of R2 lies in `vN_sa`. Evidence:
`EJA`/`JBW` admit no such tensor (the classical no-go for Jordan composites; Barnum–Graydon–
Wilce: composites of spin factors force `ℂ`-quantum theory), and Alfsen–Shultz's dynamical
correspondence `a ↦ [ , ]`-derivation is what a tensor with `M₂(ℂ)` (or `𝒜 ⊗ 𝒜ᵒᵖ`) exports.
Risk: medium-high; the derivation of a dynamical correspondence from a tensor is not written
anywhere I know; first step: `– ⊗ B(ℓ²)` should force `†`-unitaries of `X` to be inner-like.

## (ii) Modular theory: what the effectus sees, and what it does not

Setting: `𝒜` σ-finite, `ω` a faithful normal state (a state `1 → 𝒜` in `vNᵒᵖ` with `⌈ω⌉ = 1`).

**Thm M1 (centraliser = undisturbed sharp predicates).** For a projection `e`:
`e ∈ 𝒜_ω ⟺ ω(e & a) + ω(e⊥ & a) = ω(a) for all effects a`, i.e. the Lüders measurement of `e`
does not disturb `ω`. Proof: the identity says `ω(eae⊥) + ω(e⊥ae) = 0` for all `a`; substituting
`ea` for `a` gives `ω(eae⊥) = 0` for all `a`, hence `ω(ea) − ω(ae) = ω(eae⊥) − ω(e⊥ae) = 0`, i.e.
`e ∈ 𝒜_ω` (Pedersen–Takesaki: centraliser = fixed points of `σ^ω`); the converse is immediate.
`𝒜_ω` is the span of its projections, so the centraliser is `&`-definable. Risk: nil.
Corollaries expressible in the effectus: `ω` tracial ⟺ every sharp predicate is undisturbed
⟺ `ω(a & b) = ω(b & a)` for all `a, b` (the "&-symmetric" states); `σ^ω` trivial ⟺ `𝒜_ω = 𝒜`.

**Thm M2 (type is a property of the effectus object).** For a σ-finite factor `𝒜` in `vNᵒᵖ`:
type I ⟺ `SPred 𝒜` is atomistic (vn.tex §5 hereditarily atomic); finite ⟺ `𝒜` has a faithful
`&`-symmetric state; semifinite ⟺ every nonzero sharp `s` dominates a nonzero sharp `t` whose
comprehension object `{X | t}` (= `t𝒜t`) has a faithful `&`-symmetric state; type III ⟺ no nonzero
comprehension object has one. Pure *states* of an object (in the effectus sense, corner∘filter
into `1`) are the vector states of minimal projections, so type II and III objects have no pure
states but all their filters and corners; type III has moreover no `&`-symmetric state on any
corner. "Type" for an object of an abstract `†`-effectus: define it by these clauses.

**Takesaki in effectus terms (Thm, folklore).** A sharp mono `ℬ ↪ 𝒜` (an `mni`-map, i.e. a sharp
map `𝒜 → ℬ` in `vNᵒᵖ`) admits an `ω`-preserving retraction (a conditional expectation `𝒜 → ℬ`,
`ω ∘ E = ω`) iff `σ^ω_t(ℬ) = ℬ` for all `t`. So the modular group is visible as *the* invariant
governing which subobjects of `(𝒜, ω)` split. It is not itself definable from `(Pred, &, Stat)`:
its definition (KMS) is an analytic-continuation condition, and every attempt to write KMS as an
`&`-identity `ω(a & σ_t b) = …` produces three-point terms `ω(σ_t(b) √a σ_{-i}(√a))` that are not
of `&`-form. What *is* `&`-form is the boundary of KMS: `ω(a & σ_t(b)) = ω(b & σ_{-t}(a))` fails
unless `σ_t` fixes `a` or `b`, and equality for all `t` characterises `a ∈ 𝒜_ω` (by M1's method).
**Modular conjugation:** the dilation (220II) of `ω` is the GNS triple `𝒜 →ρ B(H_ω) →h 1`; the
`&`-commutant `{q ∈ [0,1]_{B(H_ω)} : q & ρ(a) = ρ(a) & q ∀a}` is `[0,1]_{𝒜'}` (Gudder–Nagy:
`&`-commuting ⟺ commuting), and Tomita says this commutant is the image of a second sharp
map `𝒜ᵒᵖ → B(H_ω)` through which `h` again gives `ω`. **Conj M3.** In a `†`-effectus with
dilations, the `&`-commutant of the dilation of a faithful state is again a dilation of the same
state on an object `X^∘` with `Pred X^∘ ≅ Pred X`, `& ` preserved (the "opposite object"). Risk:
medium; in `vNᵒᵖ` it is Tomita–Takesaki, abstractly it needs a notion of "generated by"
(`ρ(𝒜) ∨ ρ'(𝒜ᵒᵖ) = B(H)`) the effectus lacks; and `𝒜 ⊗̄ 𝒜' → B(H)` is *not* a sharp map
unless `𝒜` is type I, so M3 cannot be stated via the tensor.

## (iii) The sequential product: SEA axioms hold in `EJAᵒᵖ`; the abstract question reduces to Fuglede

eff.tex 225VI proves (S1)–(S3) in every `†`-effectus and 225VIII leaves (S4), (S5) and
"`p & q = q & p ⟹ asrt_p asrt_q = asrt_q asrt_p`" open. In an `&`-effectus `&` is already
*characterised* (uniqueness of the ⋄-positive `asrt_p`, 211II.1 = proc.tex 105V), so the right
question is whether the two known models satisfy Gudder–Greechie, and what the abstract
obstruction is.

**Thm P1 (`[0,1]_E` is a SEA for every Euclidean Jordan algebra `E`, with `a & b = U_{√a} b`).**
Sketch. Faraut–Korányi X.2.2: `a, b` operator-commute iff simultaneously diagonalised by one
Jordan frame. (S4a) `U_{√a} b = U_{√b} a ⟹ a, b` operator-commute: the subalgebra `J(a, b)` is
special (Shirshov–Cohn), hence a finite-dimensional `JC`-algebra `⊂ M_k(ℂ)_sa`, with `√a ∈ J(a)`;
inside `M_k(ℂ)` the hypothesis reads `√a b √a = √b a √b`, so Gudder–Nagy (Fuglede–Putnam,
elementary in finite dimension) gives `ab = ba`; the joint spectral projections `eᵢ(a) ∘ fⱼ(b)`
lie in `J(a, b) ⊂ E` and are orthogonal idempotents of `E`, so `a, b` operator-commute in `E`.
(S4b) then `U_{√a} b = a ∘ b`, `√(a ∘ b) = √a ∘ √b`, `U_{√a ∘ √b} = U_{√a} U_{√b}` (Peirce
multipliers `√(λᵢλⱼ)·√(μᵢμⱼ)`), giving `(a & b) & c = a & (b & c)` and `asrt_a asrt_b = asrt_b asrt_a`
— the second open problem of 225VIII. (S5) if `c` operator-commutes with `a` and with `b`, then `b`
has no Peirce components across the spectral idempotents of `c`, and `U_{√a}` preserves that
property, so `c` operator-commutes with `a & b`, and with `a ⊕ b` by linearity; commuting pairs
have `x & y = y & x`. Risk: low; the only non-formal inputs are Faraut–Korányi X.2.2, Shirshov–
Cohn and the finite-dimensional Gudder–Nagy. The same proof (with `J(a,b)` replaced by the
von Neumann algebra `W*(a, b)`) is the known `vN` case. So both examples of `†`-effectuses have
SEA predicates; 225VIII's questions are open only abstractly.

**Reduction P2 (the abstract obstruction is Fuglede).** In a `†`-effectus put `g := asrt_q ∘ asrt_p`
and assume `p & q = q & p =: c`. 215III.2 twice gives `g† g = asrt_p asrt²_q asrt_p = asrt²_c =
asrt_q asrt²_p asrt_q = g g†`: `g` is `†`-normal. (S4)/(S5) and the 225VIII question all follow
from **Conj P3: a `†`-normal composite `asrt_q ∘ asrt_p` is `†`-self-adjoint.** In `vNᵒᵖ`, P3 is
`Ad_{TT*} = Ad_{T*T} ⟹ TT* = T*T` (`T = √q√p`; `x² = Ad_x(1)`) followed by Gudder–Nagy, i.e.
Fuglede. Refutation risk for P3 in an arbitrary `†`-effectus: medium-high — Fuglede has no
order-theoretic proof, and the natural place to look for a counter-model is a `†`-effectus built
from a real or quaternionic `C*`-algebra where `T` normal does not force `T = T*` up to scalars
(`T = i·1` is normal, `Ad_T = id = Ad_{T*}` but `T ≠ T*`; note this does *not* break P3 since
`g = g† = id` — the counter-model must separate `g` from `g†`, not `T` from `T*`).

**Erratum 106III.3, corrected clause.** With `p ∗ q := √p u_p* q u_p √p`, clause (E) is
⋄-self-adjointness of `q ↦ a* q a` for `a := u_p √p`, i.e. `e₁ a e₂ = 0 ⟺ e₁ a* e₂ = 0` for all
projections. This holds when `a` is self-adjoint, i.e. when `u_p* = u_p` **and** `u_p p = p u_p`;
`u_p* = u_p` alone fails (the flip on `B(ℂ²)`, `p = diag(1, 9/25)`), and normality of `a` is also
insufficient (`a = diag(1, i)`, `v₁ = (1, x)`, `v₂ = (1, y)` with `x̄y = i`). The intended
conclusion (`u_p = g(p)`, `g` Borel `±1`-valued) already has `u_p p = p u_p`, so the fix is to
add "and `p u_p = u_p p`" to the (E) clause; the exercise's programme is unaffected. Related
open **Problem 106IV** (is (D) superfluous?): test on `M₂(ℂ)` first, where (B)+(E) with `⌈p⌉ = 1`
reduce `∗` to `√p u_p*(·) u_p √p` with `u_p √p` self-adjoint, and (C) becomes a functional equation
for `p ↦ u_p` — the unresolved question is whether it forces a square root `u_p √p ≥ 0`.

## (iv) Hilbert modules and the ultranorm: Radon–Nikodym and a Lebesgue decomposition

**Thm T1 (Paschke's Radon–Nikodym in the dilation language; Thm, known mathematics).** Let
`ψ : 𝒜 → ℬ` be ncp with Paschke dilation `𝒜 →ρ B^a(X) →h ℬ` (dils.tex; `h = ⟨e, · e⟩`). For
ncp `φ : 𝒜 → ℬ`: `φ ≤ ψ` (i.e. `ψ − φ` cp) iff `φ = h ∘ asrt_t ∘ ρ` for a unique effect `t` in the
`&`-commutant of `ρ`, `t ∈ [0,1]_{ρ(𝒜)' ∩ B^a(X)}`. (Since `t` commutes with `ρ(a)`,
`√t ρ(a) √t = t ρ(a)`, so this is Paschke 1973 Thm 5.3 verbatim; the effectus content is that
"`φ ≤ ψ`" is "`φ` factors through the dilation of `ψ` by an assert in the commutant".) Risk: nil.
**Conj T1' (abstract).** In a `†`-effectus with dilations (220II), maps below `f` correspond to
effects in the `&`-commutant of the sharp leg of `f`'s dilation. First lemma: `h ∘ asrt_t ∘ ρ ≤ f`
for such `t` (needs only `asrt_t ⊕ asrt_{t⊥} = id` on the commutant, which is R1(d) in disguise).
Risk: medium; the converse (every `φ ≤ f` arises so) is the universal property of the dilation
applied to `φ ⊕ (f − φ)`, which needs subtraction of maps — available in `vNᵒᵖ`, not in general.

**Conj T2 (module Lebesgue decomposition relative to the ultranorm).** Let `X` be a self-dual
Hilbert `ℬ`-module (`ℬ` a von Neumann algebra) and `[·,·]'` a second `ℬ`-valued semi-inner
product on `X`, not assumed bounded. Call `[·,·]'` *ultranorm-closable* if every net that is
`[·,·]'`-Cauchy and ultranorm-null has `[x_α, x_α]' → 0` ultraweakly, and *singular* if `0` is the
only closable semi-inner product below it. Then `[·,·]' = [·,·]'_ac + [·,·]'_s` with `[·,·]'_ac`
the largest closable semi-inner product `≤ [·,·]'` and `[·,·]'_s` singular; if `[·,·]'` is bounded
(`[x,x]' ≤ c⟨x,x⟩`) then `[x, y]'_ac = ⟨x, T y⟩` for a unique `0 ≤ T ∈ B^a(X)` (self-duality:
`y ↦ [·, y]'` is a bounded module functional) and the singular part vanishes on an ultranorm-
dense submodule. Plausibility: high for existence (Simon 1978 / Hassi–Sebestyén–de Snoo, run
with `ℬ`-valued forms and `f ∘ [·,·]'` for np-functionals `f`), **uniqueness of the decomposition
is false already for `ℬ = ℂ`** (Hassi–Sebestyén–de Snoo 2009: unique iff the ac part is "almost
dominated"), so the theorem must be stated with "largest closable part", not "unique
decomposition". Risk: medium; the `ℬ`-valued version of "closable" is not obviously equivalent
across the two natural choices (ultraweak vs ultranorm convergence of `[x_α, x_α]'`), and the
choice determines whether 149V's completeness (self-dual ⟺ ultranorm complete) is the engine.
Sketch: for each np-`f` the scalar form `f ∘ [·,·]'` on the Hilbert space `X ⊗_f ℬ`
(dils.tex 136II) has a Simon decomposition; show the ac parts are
compatible in `f` and reassemble by 149V(4) (orthonormal basis) — the compatibility step is the
open point. Payoff if true: a "Lebesgue decomposition of ncp maps `𝒜 → ℬ` relative to a given
one" via Paschke dilations, the module analogue of Kosaki's 1985 decomposition of normal
functionals (which uses relative modular theory — tying (iv) back to (ii)).

## Ranking

1. **P1** — a theorem now (SEA predicates for `EJAᵒᵖ`, both 225VIII questions closed in the models);
   cheapest to write up, resolves a printed open remark. 2. **M1/M2** — folklore turned into
   effectus definitions; the "type of an object" definition is publishable as is. 3. **R2** — the
   real prize, but the missing symmetry axiom is a live refutation risk and must be tested on
   Alfsen–Shultz's non-symmetric spectral convex sets before any building. 4. **T2** — genuinely
   new analysis, uniqueness already known false; state as "largest closable part". Do not spend
   on R3 or P3 without a model check first.
