# The base of the theory: which algebras, which field, which completeness — research note (2026-09-12)

Conjectural; nothing here is checked in Lean or in the theses. Anchors in the theses:
eff.tex 200II (quotient), 201II (comprehension), 204I (images), 206II (⋄), 211II (&), 215I
(†), 215III (†-theorem); vn.tex 6I (Kadison's two axioms); proc.tex 26I (pure = composites
of corners and filters). Not repeated here: `CvNᵒᵖ` repairs Giry (new-categorical-probability §3), †-effectus ⟹
JBW and tensor ⟹ `ℂ` (new-analysis-reconstruction (i)), `EJAᵒᵖ` is `&`/† (eja-dagger).

**Recurring finding: Kadison's two axioms are two effectus axioms.** Axiom 1 (bounded
directed suprema) is what quotients/comprehension for *arbitrary* effects need; axiom 2
(normal states separate) is what *images* need. C\*-algebras have neither; AW\* the first.

## (i) C\*-effectuses and the `A ↦ A**` completion

Setting: `C*ᵒᵖ` = unital C\*-algebras, cpsu maps, opposite (an effectus: Cho–Jacobs).
Predicates on `A` are the effects `[0,1]_A`, states the cpu maps `A → ℂ` (all states,
not just normal ones), sharp predicates the images.

**Prop 1.1 (commutative case = Radon kernels).** `cC*ᵒᵖ` (pu = cpsu here) is `Kl(𝓡)`
of the Radon monad on `CH` (Furber–Jacobs); Gelfand duality `CH ≃ cC*ᵒᵖ` is its
subcategory of *sharp* maps (\*-homs). It has:
* **quotients for every effect** `a ∈ C(X)`: `X/_{1−a} = β(coz a)`, i.e. the algebra
  `C_b(coz a)`, with `ξ(c) = a·c` (extended by `0`). Sketch: `ξ(1) = a`; a cpsu
  `f : B → C(X)` with `f(1) ≤ a` has `|f(b)(t)| ≤ ‖b‖ a(t)`, so `f'(b) = f(b)/a` is
  bounded on `coz a`, positive, subunital, and unique since `ξ` is injective. The vN
  analogue is `L^∞(coz a)`; in C\* the quotient object is the Stone–Čech blow-up of the
  cozero set — a first sign that quotients want completeness;
* **comprehension for every effect**: `{X | a} = C(Z)`, `Z = {a = 1}` (a zero set),
  `π = restriction`. Sketch: `g(1−a) = 0` with `g` pu gives `g((1−a)^{1/2^k}) = 0` by
  Kadison–Schwarz, so `g` kills the ideal of functions vanishing on `Z`; Tietze;
* **no images**: the point state `δ_x` at a non-isolated `x` has no least continuous
  `e ∈ [0,1]` with `e(x) = 1`. So `⌈·⌉`, `f^⋄`, `f_⋄` do not exist; `cC*ᵒᵖ` is not ⋄.
  (Consistent with eff.tex 204I.41 for `OUSᵒᵖ ⊃ cC*ᵒᵖ`.) Risk: low.

**Conj 1.2 (non-commutative: even quotients fail).** In `C([0,1], M₂)ᵒᵖ` the effect
`a = diag(x, 1)` has no quotient and `diag(1, x)` no comprehension. Evidence: the only
candidate `Q = {c ∈ ⌈a⌉A**⌈a⌉ : √a c √a ∈ A}` is not closed under products (the
`22`-entry of `cd` is `s(x)t(x)` with `s, t` bounded and discontinuous at `0`), and any
smaller C\*-algebra breaks existence, any larger one uniqueness; dually `⌊a⌋A⌊a⌋` is not
a subalgebra of `A**`. Sharp effects (projections) do have corners and filters
(`pAp`, `√a·√a` for `a = p`). So `C*ᵒᵖ` has quotients and comprehension *exactly for
sharp predicates*, not the full 200II/201II. Risk: medium (a cleverer candidate object
could exist; the refutation target is a universal factorisation through a non-obvious
C\*-algebra).

**Thm 1.3 (the completion is a coreflection).** `A ↦ A**` (universal enveloping vN
algebra) is right adjoint to the inclusion `vNᵒᵖ ↪ C*ᵒᵖ`:
`C*ᵒᵖ(M, A) = C*_cp(A, M) ≅ vN_ncp(A**, M) = vNᵒᵖ(M, A**)` (Takesaki III.2.2). Hence
`vNᵒᵖ` is *coreflective* in `C*ᵒᵖ` (not reflective: the effectus arrows run the other
way). Effectus content of the counit `ε : A** → A` in `C*ᵒᵖ`: `Stat(A**) ≅ Stat(A)`
(every state becomes normal), `Pred(A) ↪ Pred(A**)` as a sub-effect-module, and the
coreflector preserves coproducts (`(A ⊕ B)** = A** ⊕ B**`) and the scalars. It is
*not* the free/cofree ⋄-effectus on `C*ᵒᵖ` in any universal sense I can prove — the
honest statement is: **it is the largest coreflective sub-effectus of `C*ᵒᵖ` on which
states are normal**, and normality is what images need. Risk: low for the adjunction
(textbook), medium for the maximality clause.

**Cor 1.4 (Stone–hyperstonean, effectus reading).** For `X ∈ CH`, `C(X)** = C(X̂)`
with `X̂` hyperstonean (Dixmier), `= ⊕_μ L^∞(μ)` over a maximal singular family of
Radon measures. Thus `X̂` is the ⋄-coreflection of `X` in `Kl(𝓡)`: it adds exactly the
supports of Radon measures (images of states), keeps every state, and makes every
quotient `β(coz a)` collapse to a clopen. The Stone–hyperstonean passage *is* "add
images while fixing states".

**What survives on `C*ᵒᵖ`.** Square roots of effects always exist, so 215III.1 holds and
the fundamental formula holds as an identity; but `asrt_p = √p·√p` is not *pure* in the
200II sense without quotients (Conj 1.2), and sharp complement is vacuous without
images. The sharp fragment (projections, their corners and filters) is intact.

## (ii) Real vs complex: what detects `ℂ`

Facts first. Real vN algebras `M ⊂ B(H_ℝ)` (equivalently `M ∩ iM = 0` in `M ⊗ ℂ`) with
ncpu maps form an effectus; `M_n(ℍ)` is the real vN algebra `M_n(ℍ) ⊂ M_{4n}(ℝ)`; the
self-adjoint parts `Sym_n(ℝ)`, `Herm_n(ℂ)`, `Herm_n(ℍ)` are EJAs, so **real, complex and
quaternionic finite-dimensional quantum theory are all full sub-†-effectuses of `EJAᵒᵖ`**
(eja-dagger). Consequence:

**Prop 2.1 (no existing axiom sees the field).** Every axiom of eff.tex §§206–215 (⋄, &,
†, †′) holds in `Real-vN_fdᵒᵖ` and `M_n(ℍ)ᵒᵖ`. The dagger "on all maps" is not a
candidate: in `vNᵒᵖ` it is only defined on pure maps, and pure maps of `M_n(ℝ)` have the
same polar-decomposition dagger. Risk: low (it is the EJA embedding).

Two curiosities of the *real* base: `ℂ_ℝ`, `ℍ_ℝ` are objects of `Real-vNᵒᵖ` with
`Pred = [0,1]` and one state, so `Pred` does not reflect isomorphisms there (it does in
`vNᵒᵖ`); with merely *positive* maps `ℂ_ℝ` has a line of states (`ω(i)` free), so cp is
essential over `ℝ`. Real quantum theory should be read on self-adjoint parts, in `JBWᵒᵖ`.

**Thm 2.2 (qubit axiom, finite-dimensional; a theorem by classification).** Say an
`&`-effectus satisfies **Q4** if for orthogonal atoms `s ⊥ t` (sharp, minimal non-zero)
the effect module `Pred({s ∨ t})` (comprehension object) is 4-dimensional. Then a full
sub-effectus of `EJAᵒᵖ` closed under comprehension satisfies Q4 iff every object is
`⊕ᵢ Herm_{nᵢ}(ℂ)` or `ℝ`. Proof: Jordan–von Neumann–Wigner; the rank-2 faces have
predicate dimension `3` (`Sym_n(ℝ)`), `4` (`Herm_n(ℂ)`, and `V₃ = Herm₂(ℂ)`),
`6` (`Herm_n(ℍ)`), `10` (`Herm₃(𝕆)`, whose rank-2 faces are `V₉`), `n+1` (spin `V_n`).
`Pred({s∨t})` is effectus-intrinsic (affine dimension of an effect module). Risk: low.
It refutes "dagger detects ℂ" and "local tomography is needed": Q4 is a *local* axiom.

**Conj 2.3 (phase axiom, all types).** Q4 is vacuous for type II/III (no atoms). The
type-free candidate is Alfsen–Shultz's *dynamical correspondence* (1998): `M` is
`𝒜_sa` of a complex vN algebra iff there is a linear `a ↦ δ_a` into skew order
derivations with `δ_a(a) = 0` and `[δ_a, δ_b] = −[L_a, L_b]`. Effectus phrasing: to each
sharp `s` a one-parameter group `φ^s_t` of †-unitary pure maps commuting with `asrt_s`,
fixing every sharp `r ≤ s` and `r ≤ s^⊥`, additive in `s` (`φ^{s∨s'} = φ^s φ^{s'}` for
`s ⊥ s'`), whose generators satisfy the commutation law with `L_a x := ½((a ⊕ x)² −
a² − x²)` read off `p ↦ p & p`. The **test that matters**: mere *existence* of phases
does **not** detect `ℂ` — in `Herm₂(ℍ) = V₅` the †-unitaries fixing two antipodal atoms
form `SO(4)` (plenty of circles), in `Sym₂(ℝ)` only `{±1}`. Only the commutation law
kills `ℍ`: `x ↦ [ia, x]` is not well defined on `Herm_n(ℍ)` because `i` is not central
(`(iax − xia)* ≠ −(iax − xia)` unless `[a, i] = 0`), and Alfsen–Shultz show no other
choice works. So a "complex †-effectus" := †-effectus + phases + commutation law;
`M_n(ℍ)` and `M_n(ℝ)` fail it, and by Alfsen–Shultz (plus (iii)) a complex †-effectus
with normal spectral predicates embeds in `vNᵒᵖ`. Risk: medium — the effectus phrasing
of the commutation law needs `L_a` recovered from `&`, which new-analysis-reconstruction
R2 already needs; the algebraic core is a published theorem. (Counting version for the
atomic case: the stabiliser of `s, t` in the †-unitaries of `{s∨t}` is a *circle* iff
`ℂ`; `dim SO(d−1)` for the `d`-ball: `0, 1, 6, 28` for `ℝ, ℂ, ℍ, 𝕆`.)

## (iii) JBW-algebras: `JBWᵒᵖ` as a ⋄/&/†-effectus, and the one lemma

`JBW` = JB-algebras that are Banach duals (Hanche-Olsen–Størmer 4.1.1), equivalently
monotone complete with separating normal states (HOS 4.4.16 — Kadison's two axioms
again); maps: normal positive unital, opposite. Contains `vN_sa`, `EJA`, spin factors of
any dimension, `Herm₃(𝕆)`-valued algebras `C(X, Herm₃(𝕆))` (Shultz: every JBW is
`JW ⊕ C(X, H₃(𝕆))`), and type II/III factors.

**Conj 3.1.** `JBWᵒᵖ` is a †-effectus, with `asrt_a = U_{√a}`, comprehension of `a` the
Peirce corner `U_{⌊a⌋} : M → M₁(⌊a⌋)` with `⌊a⌋ = 1 − ⌈1−a⌉`, quotient of `1−a` the
filter `U_{√a} : M₁(⌈a⌉) → M`, images the range projections `r(f) := ⌈f(1)⌉`-type
least projections `e` with `f(1−e) = 0` (exist by normality). The proofs of eja-dagger
§1–2 and the †-theorem 215III go through unchanged *provided* the following holds.

**Lemma J (the single lemma; Jordan Douglas/division).** In a JBW-algebra, for
`0 ≤ a ≤ 1` and `x` self-adjoint: `−λa ≤ x ≤ λa ⟺ x = U_{√a}(c)` for some
`c ∈ M₁(⌈a⌉)` with `‖c‖ ≤ λ`, and `c` is unique. This is vn.tex 41I ("division") with
`√a·√a` replaced by `U_{√a}`. Everything else the tree's vN proofs use is available
classification-free in JBW: spectral theorem and functional calculus (HOS 3.2.4, 4.1),
range projections `⌈a⌉` and Peirce decomposition (HOS 4.2), positivity of `U_a`
(HOS 3.3.6) and the fundamental formula `U_{U_a b} = U_a U_b U_a` (HOS 2.4.18) — which
is 215III.2 verbatim — and Kadison–Schwarz `f(a)² ≤ f(a²)` for positive unital `f`
(reduce to the associative subalgebra `C(a)` and use `(λx + μ(1−x))² ≤ λ²x + μ²(1−x)`,
i.e. `x ∘ (1−x) ≥ 0`). Lemma J gives: existence/uniqueness of the mediating map of a
filter (`f' = U_{√a}^{-1} ∘ f` on `M₁(⌈a⌉)`), the corner's universal property (via
`f(1−⌊a⌋) = 0` from Kadison–Schwarz), and "pure = `U_{√φ(1)} ∘ Θ ∘ U_{⌈φ⌉}`" with `Θ` a
Jordan iso (unital order isos of JBW-algebras are Jordan isos: HOS/Isidro–Rodríguez).
Plausibility of Lemma J: high — `[−a, a] = U_{√a}[−1,1]` is the statement that
`U_{√a}(M^+)` is the face of `M^+` generated by `a`, which is Alfsen–Shultz's
face/compression theory (State spaces, ch. 1–2) in the JBW case. Risk: low-medium; the
one place finite dimension is really used in [eja] is the eigen-decomposition matching
in the uniqueness of `asrt` (eja-dagger §1, step 1), which must be replaced by a
spectral-projection argument (`Θ` fixes each spectral projection of `q`, hence `q`).

**Refutation targets.** Infinite-dimensional spin factors (type I₂, all `JW`: Lemma J
should hold verbatim); type II/III factors are `JW` (Shultz) but their *maps* are not
restrictions of cp maps, so nothing transfers from `vNᵒᵖ` — the abstract Jordan proof is
the only route, and Lemma J is where it would break.

## (iv) Boolean bases: what `CvNᵒᵖ` knows that Stonean does not

`CvN ≃ MeasAlg` (localisable measure algebras; Segal, Fremlin 32) and `CvN ≃ Hyperstoneanᵒᵖ`
(Dixmier). The naive characterisation — "⋄-effectus whose sharp predicates form a
complete Boolean algebra" — is **too weak**:

**Prop 4.1.** Let `cAW*ᵒᵖ_n` be commutative monotone-complete C\*-algebras `C(X)`, `X`
Stonean, with *normal* (monotone-continuous) pu maps, opposite. It is a ⋄-effectus:
quotients `C(coz a)` (the cozero set is open, its closure clopen; Kadison's axiom 1
supplies `⌈a⌉`), comprehension `C(⌊a⌋)`, images `IM f = ⋀{p : f(p) = 1}` (the set is
down-directed and `f` normal), sharp = clopens = a complete Boolean algebra. Yet `C(X)`
is a vN algebra only for hyperstonean `X`. Risk: low.

So ⋄ (and & and †, which are algebraic) do not know Kadison's axiom 2. What does:

**Thm 4.2 (separation).** An object `X` of an effectus is *state-separated* if
`p ∘ ω = q ∘ ω` for all states `ω : 1 → X` implies `p = q`. In `cAW*ᵒᵖ_n` the
state-separated objects are exactly the hyperstonean ones, i.e. `CvNᵒᵖ` is the full
sub-effectus of state-separated objects of `cAW*ᵒᵖ_n` (Dixmier: `X` hyperstonean iff
normal measures separate `C(X)`; Kadison's axiom 2). Non-commutatively the same
sentence with `AW*ᵒᵖ_n` and `vNᵒᵖ` is Kadison's theorem itself (vn.tex 6I). Risk: low;
the content is only the effectus *phrasing*: **`vNᵒᵖ` = ⋄ + state-separation, where ⋄
carries axiom 1 and separation carries axiom 2.**

**Characterisation (conj).** An effectus `C` is equivalent to `CvNᵒᵖ` iff: (1) ⋄ and &
with `p & q = q & p`; (2) scalars `[0,1]`, predicates normal effect modules; (3) objects
state-separated; (4) `SPred X` a complete Boolean algebra generating `Pred X` spectrally;
(5) every object a coproduct of sharp comprehensions, with all maps between them. Sketch:
(4) makes `Pred X` the unit interval of `C(Stone SPred X)` (Stone + Loomis–Sikorski),
(2)+(3) make it hyperstonean (Kelley's criterion), (1) makes `asrt` multiplication.
Refutation target: a sub-effectus with only *measure-preserving* maps satisfies (1)–(4);
(5) must force fullness. What `Set`, `Kl(𝒟_ω)` lack: (2)/(4) — atomic algebras only,
`ℓ^∞` but never `L^∞[0,1]`.

## Ranking

1. **The two-axiom reading** (Thm 4.2, Prop 4.1, Prop 1.1): lowest risk, one sentence,
   explains at once why `C*ᵒᵖ` and `Kl(𝒢)` fail and where. First test: Prop 1.1's quotient.
2. **Lemma J** for `JBWᵒᵖ`: one analytic lemma carries the `vN`/`EJA` tree to JBW,
   type II/III and `𝕆` included; risk low-medium.
3. **Q4 / phase**: Thm 2.2 is a theorem by classification; Conj 2.3 is the type-free
   form and its `ℍ`-test is decisive (phase existence is *not* enough).
4. **Conj 1.2** (`C*ᵒᵖ` lacks even quotients): likeliest to be refuted by a cleverer
   object; one afternoon on `C([0,1], M₂)`.
