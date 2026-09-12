# Categorical probability and physics foundations from the two theses

Research note, 2026-09-12. No Lean. Sources: eff.tex 180I/V, 189I, 192III (`Kl 𝒟_M`),
197II, 199II, 205I, 206II, 211II, 212III (`standard-form-map`), 221II–IV (dilations),
222 (gates, 222IV's open questions), 223II–VI (`sef_p`, `Inv`, order correspondence);
dils.tex 139I–XI (`ess-uniq-pur`), 154III (`existence-paschke`), 157IV
(`paschke-correspondence`); proc.tex 125I, 127I/III (`duplicable`). "Thm" = argued below to
the point I would bet on it; "Conj" = evidence only. A map `X → Y` of `vNᵒᵖ` is an ncpu map
`Y → X` of algebras; `⊗` is the spatial tensor; `ϱ(𝒜)'` the commutant inside `𝒫`.

---

## 1. `vNᵒᵖ` and Markov categories: the Markov core is `Kl(𝒟_ω)`, and the conditional lives on the Paschke environment

**Setting.** A Markov category (Fritz) is symmetric monoidal with a commutative comonoid
`(copy_X, del_X)` on every object, `del` natural. In `(vNᵒᵖ, ⊗, ℂ)`: `del_𝒜` is the unit
`ℂ → 𝒜`, natural since maps are unital; `copy_𝒜` would be an ncpu `δ : 𝒜 ⊗ 𝒜 → 𝒜` with
`δ(a ⊗ 1) = a = δ(1 ⊗ a)` — a duplicator with unit `1` (proc 127I asks even less: npsu).

**Thm 1.1 (Markov core).** The objects of `vNᵒᵖ` carrying a Markov comonoid are exactly the
`ℓ^∞(X)`, `X` a set; the comonoid is unique (`δ = ·`, `del = 1`); the full subcategory on them
is a Markov category isomorphic to `Kl(𝒟_ω)`, the Kleisli category of the countably-supported
distribution monad on `Set`. Its deterministic maps (Fritz: those commuting with copy) are
the nmiu maps = functions `X → Y`.
*Proof.* Existence/uniqueness/shape of `δ` is proc 127III (`duplicable`) verbatim. An ncpu
`ℓ^∞(Y) → ℓ^∞(X)` is `x ↦ (a normal state on ℓ^∞(Y))`, and normal states on `ℓ^∞(Y)` are
`ℓ^1(Y)`-densities, i.e. countably supported distributions; composition is Kleisli
composition (Chapman–Kolmogorov). Multiplicative ⇔ Dirac-valued ⇔ a function. ∎

**Fritz's axioms, read off from `Kl(𝒟_ω)`:** conditionals and Bayesian inverses exist
(discrete Bayes; a.s.-equality is equality off the support); causal, positive; but
**Kolmogorov products fail**: infinitely many `ℓ^∞({0,1})` would need an atomless normal
state on `ℓ^∞(∏X_i)`, which has none.
Sharper: `CvNᵒᵖ` (commutative algebras, vn.tex 133: `L^∞` of localisable measure spaces)
has the *objects* of `Stoch` but **no copy at all** on any atomless `L^∞(X)` — proc 127III's
continuous-measure argument is exactly the statement that the diagonal `X → X × X` has
measure zero, so `Δ^* : L^∞(X×X) → L^∞(X)` is not defined on a.e.-classes. Hence there is
no monoidal functor `Stoch → vNᵒᵖ` extending `X ↦ L^∞(X)`. Parzygnat's "quantum Markov
category" (copy = non-positive multiplication) escapes only by leaving `vN` for all linear
maps, where the dilation machinery is unavailable.

**What survives with a quantum input.** Fritz's conditional of `f : A → X ⊗ Y` given `X`
needs `copy_A` *and* `copy_X`; with `A` quantum it does not typecheck. What typechecks is
classical `X`, quantum `A, Y` — an *instrument* `f : ℓ^∞(X) ⊗ ℬ = ℓ^∞(X; ℬ) → 𝒜`, a family
`φ_x := f(δ_x ⊗ ·)` of ncp subunital maps with marginal `φ := Σ_x φ_x = f(1 ⊗ ·) : ℬ → 𝒜`.

**Thm 1.2 (Paschke as disintegration).** Let `(𝒫, ϱ, h)` be a Paschke dilation of the ncpu
`φ : ℬ → 𝒜` (dils 154III). Instruments with outcome set `X` and marginal `φ` correspond
bijectively to normal positive unital maps `ℓ^∞(X) → ϱ(ℬ)' ⊆ 𝒫` (equivalently: normal
POVMs `{t_x} ⊆ [0,1]_{ϱ(ℬ)'}`, `Σ t_x = 1`), via `φ_x = h(t_x ϱ(·))`.
*Proof.* Each `φ_x ≤_ncp φ`, so dils 157IV gives unique `t_x ∈ [0,1]_{ϱ(ℬ)'}` with
`φ_x = φ_{t_x}`; `t ↦ φ_t` is a *linear order isomorphism of intervals*, and `t ↦ h(tϱ(·))`
is normal in `t` (`h` normal), so finite sums `Σ_{x∈F} t_x ≤ 1` and the ultraweak sup `t` has
`φ_t = Σ_x φ_x = φ = φ_1`, whence `t = 1`. Conversely a POVM in the commutant gives ncp maps
`h(√t_x ϱ(·) √t_x)` summing to `φ`. ∎
So the "conditional of the classical outcome given the quantum output" exists, but not on
`ℬ`: it is a measurement on the *environment* `ϱ(ℬ)'` of the universal dilation. This is
the precise sense in which a Paschke dilation is a categorical disintegration: it is the
representing object for the functor `X ↦ {instruments with marginal φ and outcomes X}`.

**Where it stops (refuter).** A quantum outcome algebra `𝒞` — "`ψ : 𝒞 ⊗ ℬ → 𝒜` with
`ψ(1 ⊗ ·) = φ` ≅ ncpu `𝒞 → ϱ(ℬ)'`" (Arveson's commutant-lifting shape) — needs commuting
normal representations of `𝒞`, `ℬ` to extend to the *spatial* tensor; by Effros–Lance this
fails for non-injective `𝒞` (`λ ⊗ ρ` of `L(F_2)`). **Conj 1.3:** it holds for all `ℬ` iff `𝒞`
is injective.

---

## 2. Effectus with purification: CDP's postulates against eff.tex 221–223

eff.tex 221II already axiomatises "effectus with dilations" (universal factorisation
`f = ϱ ∘ h`, `ϱ` sharp total, `h` pure), and 222IV asks whether its extra assumptions
(purity of `s`, `IM s = 1`, `H` a comprehension) "follow from more general principles".
CDP's purification postulate differs in three ways, and each difference is a theorem or a
counterexample in the thesis:

1. *Uniqueness.* CDP: unique up to a reversible map on the purifying system. Thesis: unique
   up to unique isomorphism (221IV.1) — a universal property, strictly stronger. dils 139XI
   shows CDP's form is recovered from the universal one for `φ : B(H) → B(K)` only with
   hypotheses (minimality, or equal defect dimension **and finite dimension**). In infinite
   dimension two purifications of equal "size" need not be related by a unitary on the
   environment: the universal property is the correct infinite-dimensional replacement.
2. *The environment is not a tensor factor.* For a state `ω` on `𝒜`, `𝒫 = B(H_ω)`, `ϱ` the
   GNS representation, `h` the vector state; the CDP environment is `ϱ(𝒜)'`, and
   `𝒫 ≅ ϱ(𝒜) ⊗̄ ϱ(𝒜)'` iff `ϱ(𝒜)` is a type I factor. So "purifying *system*" is a
   type-I-factor notion; the general one is the relative commutant, which eff 223III
   already characterises intrinsically: `Inv ϱ = [0,1]_{ϱ(𝒜)'}` (predicates whose
   `sef_p` does not disturb `ϱ`).
3. *No `⊗`* in an effectus (eff 180III): teleportation and "purification of transformations
   via Choi" are out of scope — but Paschke purifies transformations *directly*.

**Proposed axiom (environment).** In an &-effectus with dilations and the order
correspondence (223V), say a dilation `(P, ϱ, h)` of `f : X → Y` *has an environment* if
there is an object `E` and a sharp total `ε : P → E` whose predicate map
`ε^* : Pred E → Pred P` is injective with image `Inv ϱ`. In `vNᵒᵖ`: `E = ϱ(𝒜)'`, `ε` the
inclusion (nmiu). Then `Pred E ≅ Inv ϱ ≅ ↓f` and `Aut(E)` is CDP's group of "reversible
transformations of the purifying system".

**Thm 2.1 (no information without disturbance, effectus form).** In an &-effectus with
dilations having the order correspondence, every `g ≤ id_X` equals `asrt_p` for a unique
`p ∈ Z(X) := Inv(id_X) = {p : asrt_p ⋎ asrt_{p^⊥} = id}`; hence any instrument
`{g_x}` with `⋎ g_x = id_X` consists of `asrt_{p_x}`, `p_x ∈ Z(X)`, `⋎ p_x = 1`.
*Proof.* `(X, id, id)` is a dilation of `id_X` (221IV.3); the order correspondence for it
reads `↓id ≅ Inv(id)`, `g = id ∘ asrt_{Θ(g)} ∘ id`. ∎
In `vNᵒᵖ`: `sef_p = id` iff `p` is central (223III with `ϱ = id`, `Z(X) = [0,1]_{Z(𝒜)}`),
so non-disturbing instruments measure exactly the *centre* — CDP's theorem for factors,
with the superselection correction for free. This is CDP's NIWD *from the thesis's own
axioms*, needing neither `⊗` nor causality.

**Thm 2.2 (reversibility of pure maps).** eff 212III: `f = π_{IM f} ∘ g ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}`
with `g` total faithful; for pure `f` in a †-effectus `g` is pure total faithful, and I
claim such `g` are isomorphisms (in `vN`: a unital faithful corner∘filter is an iso; effectus
proof to be checked against 215/216 — flag). This is CDP's "pure transformations are
reversible on their support", with support `⌈1∘f⌉` and image `IM f`.

**What refutes the programme.** 222IV's Hadamard needed `H` to be a comprehension by
hand; if the environment axiom does not force it (test: `vNᵒᵖ` with `P = M_2`,
`E = ϱ(ℂ²)' = diagonal` — `E` is classical, so `Aut(E) = ℤ/2` cannot produce `H`), then
purification-without-`⊗` yields NIWD and reversibility but not the gate algebra, and
teleportation/CNOT genuinely need a monoidal effectus. I expect exactly this split.

---

## 3. Effectuses from monads: images are the obstruction, and `CvNᵒᵖ` is the repair

eff 192III: `Kl(𝒟_M)` is an effectus with scalars the effect monoid `M`. Which Kleisli
categories are ⋄-effectuses (206II: quotients, comprehension, images, `s^⊥` sharp)?

**Thm 3.1.** `Kl(𝒟)` and `Kl(𝒟_ω)` (finite / countable support on `Set`) are ⋄-effectuses:
predicates `[0,1]^X`; comprehension `{p = 1} ↪ X`; quotient `X/_p = {p ≠ 1}` with
`ξ_p(x) = p^⊥(x)|x⟩` (the mediating map divides pointwise by `p^⊥(x)`); sharp = `{0,1}`-valued
(205I: every image is `1_S`); image of `f` = union of supports. `Kl(𝒟_ω)` is the Markov
core of `vNᵒᵖ` (Thm 1.1), so it inherits this from `vNᵒᵖ` as well.

**Thm 3.2 (Giry).** `Kl(𝒢)` on measurable spaces has quotients and comprehension (same
formulas; measurability of `f(x)/p^⊥(x)` is pointwise), and its sharp-candidate
predicates `1_S` have sharp complements — but it **has no images**: the state
`λ : 1 → [0,1]` (Lebesgue) has no least measurable `S` with `λ(S^c) = 0`. So `Kl(𝒢)` is
not a ⋄-effectus, and `⌈·⌉`, `f_⋄`, `f^⋄`, ⋄-adjointness are unavailable. The same
`λ`-type argument kills the expectation monad `ℰ` (non-normal states of `ℓ^∞(ℕ)`: a
non-principal ultrafilter has no least support) and the valuation monad on `Top` (opens
are closed under unions so images exist, but `1 − 1_U` is not lower semicontinuous, so
`s^⊥` is not sharp). Sub-distributions on ω-cpos: comprehension `{p = 1}` is an up-set,
hence a sub-dcpo; images fail as in `𝒢` (uniform valuation on `[0,1]`).

**Repair.** Passing from measurable spaces to measure algebras — `X ↦ L^∞(X)`, `CvNᵒᵖ` —
restores images (support projection of a normal state) and makes `CvNᵒᵖ` a ⋄-effectus
(corners/filters of commutative algebras are commutative), at the price of copy
(Thm 1.1) and dilations (eff 221.31). So the three classical repairs pull apart:
`Kl(𝒢)` has copy but no images; `CvNᵒᵖ` has images but neither copy nor dilations; only
`Kl(𝒟_ω)` has copy and images, and it has no Kolmogorov products.

**Conj 3.3 (criterion).** For an affine commutative monad `T` on `Set` whose Kleisli
category is an effectus with scalar effect monoid `M` (eff 192III's family and its
submonads), `Kl(T)` is a ⋄-effectus iff every `ω ∈ T(X)` has a least support `supp ω`
with `ω(supp ω) = 1` and `T` restricts along `supp ω ↪ X`. Necessity: image of the state
`ω : 1 → X`; sufficiency: pointwise as in Thm 3.1, `IM f = ⋃_x supp f(x)`. Refuter: a `T`
with least supports whose sharp predicates are not exactly the `{0,1}`-valued ones.

---

## 4. Relative entropy: the measured one is effectus-intrinsic; additivity needs `⊗`

**Definition (in any effectus with scalars `[0,1]`).** For states `σ, ρ : 1 → X` put
`D_meas(σ‖ρ) := sup_{n, t : X → n·1} KL(σ∘t ‖ ρ∘t)`, the sup over finite tests
(`n·1 = 1 + ⋯ + 1`) of classical KL of the induced distributions.

**Thm 4.1.** `D_meas` is monotone under every map (`f∘t` is a test), agrees with KL on
`Kl(𝒟)`, and is the *least* function on pairs of states that is monotone and extends KL:
any such `D'` has `D'(σ‖ρ) ≥ D'(σ∘t‖ρ∘t) = KL(σ∘t‖ρ∘t)` for every test `t`. In `vNᵒᵖ` on
`M_n` it is the measured relative entropy, strictly below Umegaki for non-commuting pairs
and *not* additive under `⊗` (superadditive only). It exists verbatim on `EJAᵒᵖ`.

**Thm 4.2 (regularisation).** In a monoidal effectus `D_reg(σ‖ρ) := lim_n D_meas(σ^{⊗n}‖ρ^{⊗n})/n`
exists (Fekete) and is monotone; on finite-dimensional `vNᵒᵖ` it is Umegaki's `D`
(Hayashi–Petz pinching; Berta–Fawzi–Tomamichel 2017): Umegaki is *characterised* as the
regularised least monotone extension of KL. Müller-Hermes–Reeb (2017) give monotonicity
under all positive maps, i.e. under `EJAᵒᵖ`'s morphisms between complex matrix algebras.

**Conj 4.3 (EJA).** On the monoidal subcategory of special EJAs with the
Barnum–Graydon–Wilce composite, `D_reg(σ‖ρ) = ⟨σ, log σ − log ρ⟩` (Jordan functional
calculus, trace form), and it is monotone under all positive unital maps between EJAs.
Plausible: the pinching argument only needs the spectral idempotents of `ρ^{⊗n}` (which
generate an associative subalgebra) and the pinching inequality `σ ≤ N Σ_i U_{e_i} σ`;
the latter is the unknown for spin factors. **Refuter:** the Albert algebra has no
composite at all, so no additivity axiom can pin down `D` there — on `EJAᵒᵖ` as a whole
only `D_meas` (Thm 4.1) is canonical, and "the" relative entropy is a property of the
monoidal fragment, not of the effectus.

---

## Verdict

Best single item: **Thm 1.2 with Thm 2.1** — the pair says that in `vNᵒᵖ` the conditional
of a classical outcome given a quantum output is a POVM on the Paschke environment
`ϱ(ℬ)'`, and that NIWD is the special case `ϱ = id` where the environment is the centre.
Both are one-line consequences of dils 157IV + eff 223V that the theses never draw, and
they answer eff 222IV's "more general principles" question for two of CDP's theorems
without a tensor product. Thm 3.2 (Giry has no images) is the cleanest negative result and
worth a remark in eff 206. Section 4 is literature-bound; its thesis-native content is Thm 4.1.
