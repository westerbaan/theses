# Monoidal structure and universal algebra of effectuses — research note (2026-09-12)

Sources: proc.tex 108II (definition of the tensor by product functionals), 113II (mi-bilinear ⇒ cp),
114I–II (universal property, uniqueness), 115II/VII (functoriality, `tensor-characterization`),
117III (`⊗` distributes over `⊕`), 118II/IV (`⌈a⊗b⌉ = ⌈a⌉⊗⌈b⌉`, `⌈f⊗g⌉ = ⌈f⌉⊗⌈g⌉`), 119V
(`W_miu, W_cp, W_cpu, W_cpsu` symmetric monoidal, unit `ℂ`), 123I–II (`ℓ^∞`, `nsp` strong monoidal),
127III (duplicable ⟺ `ℓ^∞(X)`); eff.tex 173I (partial-form axioms), 192II–VII (`𝒟_M`, `Kl(𝒟_M)`
an effectus with scalars `M`, states are `M^op`-convex), 193V (coproducts of `AConv_M`), 204I
(sharp maps = nmiu), 206II (⋄-positive), 208II (`&`-effectus), 215I/III (`†`-effectus), 222I–IV
(abstract qubit, `X`, `H`, the open question), 223II–III (`sef_p`, `Inv`), 225VIII.
Not repeated here: the linear-logic model (`new-semantics-logic` iii), Jordan→vN reconstruction
through a tensor (`new-analysis-reconstruction` R3), regularised entropy (`new-categorical-probability` 4).
Everything below is conjecture-with-sketch unless marked Thm and proved in a named example.

## (i) Monoidal effectuses, and what 222IV is really asking

**Definition.** A *monoidal effectus* is an effectus `C` (total form) with a symmetric monoidal
structure `(⊗, I)` such that (A1) `I = 1`; (A2) `⊗` distributes over `+`: the canonical maps
`X⊗Y + X⊗Z → X⊗(Y+Z)` and `0 → X⊗0` are isos. A *monoidal ⋄/&/†-effectus* adds
(A3) `π_p ⊗ π_q` is a comprehension and `ξ_p ⊗ ξ_q` a quotient; (A4) `⊗` restricts to a
`†`-functor on `Pure C` (pure ⊗ pure is pure, `(f⊗g)† = f†⊗g†`).

**Thm 1 (scalars).** In a monoidal effectus the scalar effect monoid `M = End(1)` is commutative,
and `λ ⊗ μ = λ ∘ μ`. *Proof.* Eckmann–Hilton on `End(I)`, `I = 1`. ∎
Consequence: `Kl(𝒟_M)` for a non-commutative `M` (e.g. the unit interval of upper-triangular
`2×2` real matrices with the entrywise cone — an effect monoid since the cone is multiplicative)
admits *no* monoidal-effectus structure; for commutative `M` the cartesian product is one,
because `𝒟_M` is then a commutative monad. So (A1)+(A2) already single out commutative scalars.

**Prop 2 (partial form).** (A2) makes `Par C` symmetric monoidal with `⊗` bi-additive on the
PCMs: for `f: X ⇀ Y`, `g: X' ⇀ Y'` put `f ⊗ g := [κ₁, κ₂!, κ₂!, κ₂] ∘ (f⊗g)` through
`(Y+1)⊗(Y'+1) ≅ Y⊗Y' + Y + Y' + 1`. Predicates get `p ⊗ q : X⊗Y ⇀ 1`, states `σ ⊗ τ`,
marginals `X ⊗ Y → X ⊗ 1 = X` (A1), and `1∘(f⊗g) = (1∘f)⊗(1∘g)`. In `vNᵒᵖ` this is 115II
restricted to subunital maps; in `Kl(𝒟)` it is the product of subdistributions.

**Thm 3 (how `⊗` meets the ⋄-structure in `vNᵒᵖ`; all predicates, not only sharp).**
(a) `⌈p⊗q⌉ = ⌈p⌉⊗⌈q⌉` and `⌊p⊗q⌋ = ⌊p⌋⊗⌊q⌋` (118II; for `⌊·⌋`: `r ≤ p⊗q ≤ p⊗1` forces
`r ≤ ⌊p⌋⊗1`, the eigenprojection at 1, and symmetrically; commuting projections meet by product).
(b) `π_p ⊗ π_q` is a comprehension **of `p ⊗ q`** (corner of `⌊p⌋⊗⌊q⌋`, by (a)).
(c) `ξ_p ⊗ ξ_q` is a quotient **of `(p^⊥ ⊗ q^⊥)^⊥ = p⊗1 + 1⊗q − p⊗q`**, *not* of `p⊗q`
(codomain `⌈p^⊥⌉A⌈p^⊥⌉ ⊗ ⌈q^⊥⌉B⌈q^⊥⌉`, the corner of `⌈p^⊥⊗q^⊥⌉` by (a); the map is
`√p^⊥ · √p^⊥ ⊗ √q^⊥ · √q^⊥`). Comprehension is a conjunction, quotient a disjunction.
(d) `asrt_{p⊗q} = asrt_p ⊗ asrt_q` (`√(p⊗q) = √p⊗√q`), and `sef_{p⊗1} = sef_p ⊗ id`.
(e) `⌈f⊗g⌉ = ⌈f⌉⊗⌈g⌉` and `(f⊗g)_⋄(s⊗t) = f_⋄(s)⊗g_⋄(t)` (118IV), so `(f⊗g)^⋄ = f^⋄⊗g^⋄`
on product sharp predicates; `im(f⊗g) = im f ⊗ im g`.
In `Kl(𝒟)` every clause holds verbatim (`{S}×{T} = {S×T}`, `(X∖S)×(Y∖T) = (X×Y)∖(S×Y ∪ X×T)`).
**Conj 3′.** In an abstract monoidal `†`-effectus with (A3)–(A4), (d) follows: `asrt_p⊗asrt_q`
is `†`-positive (`(a†a)⊗(b†b) = (a⊗b)†(a⊗b)`) with `1∘(asrt_p⊗asrt_q) = p⊗q`, and
`†`-positive maps are the asserts (215I.3 with uniqueness in 208II.1). Risk: low, given the
identification "`†`-positive = some `asrt`" which the tree has for `vNᵒᵖ` but which needs the
abstract 215I.3 plus square roots. (b),(c) do *not* follow from (A1)–(A2): they *are* (A3).

**The phase group — the invariant 222IV is missing.** In a `†`-effectus and for a sharp `s` on
`X` put `Φ(s) := { u ∈ Pure(X,X) : u†u = uu† = id, u∘π_s = π_s, u∘π_{s^⊥} = π_{s^⊥} }`.
*Thm 4.* In `vNᵒᵖ`, `Φ(e) = { ad_{e + θe^⊥} : |θ| = 1 } ≅ U(1)` when `e` is not central
(trivial when central): the condition `eU^*aUe = eae ∀a` forces `Ue = θe` (test on rank-one
`a` in the corner), likewise `Ue^⊥ = θ'e^⊥`. In `Kl(𝒟)`, `Φ(S)` is trivial (a bijection fixing
`S` and `X∖S` pointwise). In `EJAᵒᵖ` (`†`-unitaries = Jordan automorphisms, `eja-dagger.md` §3),
for a primitive idempotent of the spin factor `V_n`: `Φ(e) ≅ O(n−1)` — so `O(2) ⊋ SO(2) = U(1)`
for `V_3 = M₂(ℂ)_sa`: the extra element is complex conjugation, which is a Jordan automorphism
but not cp. The phase group *sees orientation* (Alfsen–Shultz's dynamical correspondence is
exactly a choice of the `SO(2) ⊂ O(2)`), and is non-abelian for the quaternionic qubit `V_5`.

**Thm 5 (CNOT in `vNᵒᵖ`, answering the "can we define CNOT" half of 222IV).** With the 222
data (`P = M₂`, `e`, `h`, `s`, `X`, `H`), `Z := H∘X∘H`, and `σ` the braiding, the CNOT is the
unique total `†`-unitary `g` on `P⊗P` with (a) `g∘(π_e⊗id) = π_e⊗id`, (b) `g∘(π_{e^⊥}⊗id) =
π_{e^⊥}⊗X`, (c) `g∘g = id`, (d) `(H⊗H)∘g∘(H⊗H) = σ∘g∘σ`. *Proof.* (a),(b) force `g = ad_U`,
`U = e⊗1 + θ e^⊥⊗X` (the Thm 4 argument applied to `e⊗1`); the ambiguity is exactly
`Φ(e)⊗id`. (c) gives `θ = ±1`; `θ = −1` is `(Z⊗1)·CNOT`, and (d) separates it: conjugating
by `H⊗H` turns `Z⊗1` into `X⊗1` while `σ` turns it into `1⊗Z`. ∎ Without (d) *nothing*
built from comprehensions, restrictions and involutivity separates `CNOT` from `(Z⊗1)CNOT`.
**Candidate answer to 222IV.** (1) In any monoidal `†`-effectus the *controlled gate* `c_s(f)`
(a `†`-unitary on `X⊗Y` restricting to `π_s⊗id` and `π_{s^⊥}⊗f`) is determined by its
restrictions only up to the coset `Φ(s)⊗id`; its existence is a new axiom (A5) — it is the
`+`-cotupling `[id, f]` transported along `{s} + {s^⊥} → X`, which the effectus can form only
when `X` *is* the coproduct, i.e. classically. (2) The usual gate identities (`CNOT² = id`,
`(H⊗H)CNOT(H⊗H) = σCNOTσ`, `CNOT(X⊗1)CNOT = X⊗X`, `CNOT(1⊗Z)CNOT = Z⊗Z`) are identities
in `Pure(vNᵒᵖ)` modulo `U(1)`; whether they are *derivable* from (A1)–(A5)+222 is the true
content of 222IV, and Thm 4 predicts the answer depends on `Φ`: a model with `Φ(s) = O(2)`
(a monoidal effectus of "unoriented qubits", if one exists — `EJAᵒᵖ` has no `⊗`, see (ii))
would satisfy the same axioms with a CNOT that is not `†`-conjugate to the complex one.
(3) 225VIII (does `p&q = q&p` force `asrt_p asrt_q = asrt_q asrt_p`?) is what makes
"commuting" definable in (ii); in a monoidal effectus `p⊗1` and `1⊗q` commute in *both*
senses, so the tensor supplies the first non-trivial commuting pairs of non-sharp predicates.
Refutation targets: a `†`-effectus in which `Φ(s)` is not a group (closure under `∘`, `†`
is clear; totality of `u∘v` is clear) — none; the sharp-`a` step in Thm 4 uses that `eAe`
has rank-one effects, so for type II/III factors `Φ(e)` must be recomputed (`Ue = θe` still
follows from `(Ue)^*a(Ue) = eae` for all `a` in the corner by taking `a` a projection and its
complement in the corner — I expect the same answer).

## (ii) Is the spatial tensor characterised inside the effectus? No — and what is

**Definition.** In an `&`-effectus a *commuting span* is a pair of sharp total maps
`f: Z → X`, `g: Z → Y` (204I: nmiu in `vNᵒᵖ`) with `asrt_{p∘f} ∘ asrt_{q∘g} = asrt_{q∘g} ∘
asrt_{p∘f}` for all predicates `p, q` (in `vNᵒᵖ`: commuting ranges, since ranges are spanned
by effects). A *commuting tensor* `X ⊗_u Y` is a universal commuting span.

**Thm 6 (`vNᵒᵖ`).** `A ⊗_u B` exists for all `A, B`: it is `(1−z)(A ∗ B)` where `A ∗ B` is
the coproduct in `W_miu` (free product; exists by AFT) and `z` the central projection
generating the ultraweakly closed ideal of the commutators `[ι_A(a), ι_B(b)]` (ideals are
`zM`). The pair `a ↦ a⊗1`, `b ↦ 1⊗b` gives a surjective nmiu `A ⊗_u B → A ⊗̄ B`, and it is an
iso iff every pair of commuting normal representations of `A`, `B` factors through the spatial
tensor. This **fails** for `A = B = L(F₂)`: `λ`, `ρ` on `ℓ²(F₂)` commute, and `λ ⊙ ρ` is
min-continuous iff `F₂` is amenable (Effros–Lance; Brown–Ozawa 6.2.7), while by Effros–Lance
`‖·‖_nor = ‖·‖_min` on `A ⊙ B` for all `B` iff `A` is injective. So 114I is a universal property
*among normal bilinear maps*, whose normality (112II, via the tensor-product topology) is not an
effectus notion, and the spatial tensor is **not** the internal commuting tensor. What *is*
internal is 108II(2)(3): `A ⊗̄ B` is the largest quotient of `A ⊗_u B` on which product states
exist and are faithful — in Barnum–Wilce terms, `⊗_u` is the maximal composite, `⊗̄` the
composite "generated by product effects with product states faithful", and the gap between
them is exactly non-injectivity. Risk: low (all cited); the only claim of mine is the
construction of `⊗_u` by the ideal quotient and the identification of the kernel of
`⊗_u → ⊗̄` with the `nor`/`min` gap, which is a direct translation.

**Thm 7 (`Kl(𝒟)`, `Set`).** Every span in `Kl(𝒟)` commutes (asserts are pointwise
multiplications); the universal *sharp* commuting span is `X × Y` with the projections (sharp
total maps are functions), and it is the monoidal product; a universal span among *all* total
maps does not exist for `|X|,|Y| ≥ 2` (couplings are not unique). So the commuting-span
universal property must quantify over sharp maps, as in Thm 6, which is also why 114I needs
the "sharp" clauses (mi-bilinear) to produce nmiu extensions.

**Conj 8 (`EJAᵒᵖ`, allowing the zero algebra).** Commuting tensors exist and are computed by:
(a) `A₃(𝕆) ⊗_u B = 0` for every simple non-commutative `B` (e.g. `V₃`). *Proof.* For a
commuting span into `C = ⊕ Cᵢ` simple, each nonzero `Cᵢ` contains the Albert algebra unitally,
hence is exceptional, hence *is* the Albert algebra; `ψᵢ(B)` operator-commutes with all of it,
so lies in the centre `ℝ1`, impossible for a unital hom from a simple non-commutative `B`. ∎
(b) `V₃ ⊗_u V₃ ≅ M₄(ℂ)_sa ⊕ M₄(ℂ)_sa`, the two summands being `(M₂⊗1, 1⊗M₂)` and
`(M₂⊗1, 1⊗(M₂)^t)`: the partial transpose is not a Jordan map, so the two relative orientations
are inequivalent, and spin factors receive no commuting pair of `V₃`s (`[L_a,L_b] = 0` in a
spin factor forces `a ∥ b`). The orientation doubling is Thm 4's `O(2)/SO(2)` seen by the
tensor. Refutation risk: **medium-high** — (b) needs "every EJA generated by two operator-
commuting unital copies of `V₃` is special", which is beyond Shirshov–Cohn (four generators),
and Hanche-Olsen's universal reversibility caveats for `JC`-tensor products are precisely about
low-dimensional spin factors. First test: search for two operator-commuting unital `V₃`s in
`H₃(𝕆)`; if none, (b) reduces to a classification inside `M₄(ℂ)` and `M₂(ℍ)`
(the latter has none: the commutant of `ℂ` in `ℍ` is `ℂ`).

## (iii) Free effectuses

**Thm 9 (initial effectus with scalars `M`).** For any effectus `C` with scalars `M`, the
full subcategory on the finite copowers `n·1` is `Kl(𝒟_{M^op})_fin`: `Hom(n·1, m·1) ≅
Hom(1, m·1)^n ≅ 𝒟_M(m)^n`, and cotupling composes as `(μ ∘ λ)_{xi} = ⊕_j μ_{ji} ∘ λ_{xj}`,
the Kleisli product for `M^op` (192VII's convention). Hence `Kl(𝒟_M)_fin` is *initial* among
effectuses with scalars `M^op` and functors preserving `1`, finite coproducts and scalars, and
"the free effectus on the effect monoid `M`" with no generating objects is `Kl(𝒟_M)_fin`.
Risk: low; it is the folklore "`n·1` is `𝒟(n)`" made functorial. Two re-readings: (1)
`Kl(𝒟_M)_fin^op` is the Lawvere theory of abstract `M`-convex sets (a finitary monad's
Kleisli category on finite sets is the opposite of its theory), so 193's `AConv_M` is its
category of models, 193V's coproduct is the coproduct of models, and 192VII's
`Stat: C → AConv_{M^op}` is the nerve of the inclusion `Kl(𝒟_{M^op})_fin ↪ C`
(`Stat X = Hom(1, X)` with `Hom(n·1, X)` supplying the `n`-ary operations). (2) The PROP
presentation over `⊕` is the theory's: generators `⟨λ₁,…,λₙ⟩: 1 → n`, relations = the
barycentric-calculus axioms of `M`-convex combinations; over `×` (for commutative `M`) it is
Fritz's presentation of `FinStoch`, with `M` in place of `[0,1]`.

**Prop 10 (free ⋄-effectus on no generators).** `Kl(𝒟_M)` has comprehension and images for
every `M` (`{p} = p^{-1}(1)`, `im f = ⋃ supp`), and quotients iff `M` is an effect divisoid
(eff.tex `dfn-effect-divisoid`): `ξ_p(x) = p^⊥(x)|x⟩` on `X/p = {x : p(x) ≠ 1}` needs the
factorisation `f(x)/p^⊥(x)`, and the divisoid axioms are exactly uniqueness of that quotient.
Comprehensions and quotients of `n·1` are again copowers, so `Kl(𝒟_M)_fin` is the initial
⋄-effectus with scalars `M^op` when `M` is a divisoid — adding quotients/comprehensions
freely adds *nothing* without generators. Risk: low-medium (the "iff" for quotients).

**On free ⋄-effectuses with generators.** The partial form (173I) is a *Horn* theory:
PCM-enrichment and the partial biproduct equations `pproj_i κ_j = δ_ij`,
`κ₁pproj₁ ⊕ κ₂pproj₂ = id`, plus the clauses `1∘f ⊥ 1∘g ⇒ f ⊥ g`, `1∘f = 0 ⇒ f = 0`. Free
models therefore exist (initial-model theorem for Horn theories; Arbib–Manes-style matrix
categories over the free PCM of paths), and quotients/comprehensions are essentially algebraic
(operations `ξ_p, π_p` with equations plus uniqueness clauses), so free ⋄-effectuses on a
signature exist abstractly. I have no syntactic description beyond "matrices of paths modulo
forced sums"; the free `&`-effectus is the hard one, since 208II.2 ("`ξ∘π` is pure") is
existential. Conj: the free `&`-effectus on one object `X` with `Pred X` freely `M` has
`Hom(X,X) = M·id` and is equivalent to `Kl(𝒟_M)_fin` again — generators without states
collapse. Risk: medium.

## (iv) Traces

**Thm 11 (`⊕`-trace).** `Par(vNᵒᵖ)` and `Par(Kl(𝒟))` have countable `⊥`-sums with
`∘` continuous (increasing bounded sequences of normal positive maps converge in norm on
positive elements, and the limit is normal), so by Haghverdi's theorem they are traced for the
*coproduct* tensor with the Kleene trace `Tr^U(f) = f_{XY} ⊕ ⊕_{n≥0} f_{UY} f_{UU}^n f_{XU}`
— the semantics of quantum `while`. This is not in the theses and is orthogonal to the dcpo
enrichment of `new-semantics-logic` (i). The trace of a pure map is not pure (a countable
orthogonal sum of `ad_{T_n}`), so it does not restrict to `Pure` and does not commute with
Paschke dilation: the dilation of `Tr f` is not a trace of the dilation of `f`.

**On `⊗`-traces.** `W_cp` on finite-dimensional algebras is compact closed (`CPM(FdHilb)`),
so the *unnormalised* trace exists there; on the effectus (subunital) maps `Tr^U(id_U) = dim U`,
so the identity is untraceable and no total trace exists on `Par(vNᵒᵖ_fd)`. Haghverdi–Scott's
*partial* trace with domain `T = {f : the compact trace of f is subunital}` satisfies yanking
(`Tr σ_{U,U} = id`), naturality and dinaturality on the nose; the closure clause of vanishing II
(`Tr^V f` undefined while `Tr^{U⊗V} f` defined) is the refutation target. `B(ℓ²)` and
`ℓ^∞(ℕ)` are not dualisable in `W_cp` (no normal cup), so nothing extends past finite
dimension. Risk: medium; not pursued further.

## Ranking
1. Thm 4 + Thm 5 (phase group; CNOT pinned by Hadamard-symmetry, ambiguity `= Φ(s)⊗id`).
2. Thm 6 (spatial tensor is *not* the internal commuting tensor; Effros–Lance gap).
3. Conj 8(b) (`V₃ ⊗_u V₃ = M₄(ℂ)_sa ⊕ M₄(ℂ)_sa`, orientation doubling).
4. Thm 9 (`Kl(𝒟_M)_fin` initial; `AConv_M` = models of its opposite).
