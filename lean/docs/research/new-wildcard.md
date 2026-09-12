# Wildcard: four connections the theses never make

Research note, 2026-09-12. No Lean. Everything below is derived from the print
(`proc.tex` §1020–1040 ⋄-calculus, rigidity; `dils.tex` §1540 Paschke, §1082
Stinespring-is-Paschke; `eff.tex` §2060 ⋄-effectuses, OMLatGal functor; `proc.tex`
§1260 duplicators) and from standard results in the target fields. None of the
target fields (optimal transport, zero-error information theory / quantum
relations, ergodic theory of channels, incidence geometry) is cited in any of the
five thesis files (grep: Wasserstein, Weaver-as-relations, confusab, Perron,
subharmonic, Faure, Wigner, projective geometr — all absent).

Conventions. Heisenberg picture throughout: a channel is an ncp map
φ: ℬ → 𝒜 (ℬ = output, 𝒜 = input). `f^⋄(p) = ⌈f(p)⌉`, `f_⋄(e) = ⌈e f(·) e⌉`
(print `proc` 1020IV); for an atom ψ of the input, `φ_⋄(ψ)` is the support of the
output state `ω_ψ ∘ φ`. Paschke dilation of φ: `φ = h ∘ ϱ` via `𝒫`, ϱ nmiu, h pure,
`𝒫 = B^a(ℬ ⊗_φ 𝒜)` (adjointable maps on the self-dual completion).

---

## 1. Optimal transport: the Paschke object *is* the coupling space

**Claim.** For a stochastic kernel `k: X ⇝ Y` between finite sets, written as the
ncp map `φ: ℓ^∞(Y) → ℓ^∞(X)`, `φ(g)(x) = Σ_y k(x,y) g(y)`, the Paschke dilation is

    𝒫 = ⊕_{x∈X} M_{|S_x|}(ℂ),   S_x = { y : k(x,y) > 0 },
    ϱ(g) = ⊕_x diag(g|_{S_x}),   h(T)(x) = ⟨ξ_x, T_x ξ_x⟩,  ξ_x = Σ_y √k(x,y) e_y.

**Sketch.** `ℓ^∞(Y) ⊗_φ ℓ^∞(X)` has `⟨e_y⊗e_x, e_{y'}⊗e_{x'}⟩ = δ δ k(x,y) e_x`, so it
is the ℓ^∞(X)-module `∏_x ℓ²(S_x)`; self-dual modules over ℓ^∞(X) are exactly
such products and their adjointables are `∏_x B(ℓ²(S_x))`. `h = ⟨ξ,·ξ⟩` is a vector
state fibrewise, hence pure (corner after filter) as the print demands; ϱ is the
diagonal embedding, nmiu.

**Consequences.**
- The classical transport plan `π(x,y) = μ(x)k(x,y)` of a source measure μ is
  `μ∘h` restricted to the diagonal `ℓ^∞(⊔_x S_x) ⊆ 𝒫`. The Paschke object is the
  coupling support *plus its coherences*; the minimality clause of the dilation
  is minimality of the coupling space.
- `𝒫` is commutative iff every `|S_x| = 1` iff k is deterministic: **Monge maps
  are exactly the kernels with a classical Paschke object.** Kantorovich
  relaxation = passing from nmiu to ncp is, on the Paschke side, passing from
  commutative to non-commutative 𝒫.
- A transport cost `c: X×Y → ℝ` is a predicate on the diagonal of 𝒫, so
  `W_c(μ,ν) = inf { μ(h_k(c)) : k with ν = μ∘k }` — the Monge-Kantorovich problem
  stated in `vNᵒᵖ` without ever forming `X×Y`; the general-𝒜 version replaces
  `X×Y` by the Paschke object of a coupling channel, which is *not* `𝒜⊗ℬ`.
- The duplicator theorem (print `proc` 1270: ⊗-monoids in `W_miu` are `ℓ^∞(X)`)
  is the structural reason behind the known pathology of channel-based quantum
  Wasserstein distances (self-distance `W(ρ,ρ) ≠ 0` for mixed ρ): a coupling
  of ω with itself that is *natural in nmiu maps* would be a duplicator.

**Refutation.** Compute the Paschke object of the 2×2 kernel `k = ½·J` directly
from the print's definition; if it is `ℓ^∞(4)` rather than `M_2 ⊕ M_2`, the whole
section is dead. (I believe `M_2 ⊕ M_2`: ξ_x is a genuinely superposed vector.)
The self-distance remark needs a real theorem: "for every X in a monoidal
⋄-effectus, a natural family of self-couplings exists iff X is duplicable".

---

## 2. Zero-error information / non-commutative graphs: the ⋄-shadow, stabilised

**Claim A (identification).** For φ: M_m → M_n with Kraus form
`φ(y) = Σ K_i^* y K_i`, the Duan–Severini–Winter confusability operator system
`S_φ = span{K_i^* K_j}` equals `h(𝒫)`, the image of the pure leg of the Paschke
dilation. (`dils` 1082: `𝒫 = B(𝒦)`, `h = ad_V`, and `V^* B(𝒦) V = span K_i^*K_j`.)
So `S_φ := ultraweak closure of h_φ(𝒫_φ) ⊆ 𝒜` defines a confusability system for
every ncp map between von Neumann algebras — the DSW graph in Paschke generality.

**Claim B (⋄ captures one-shot zero-error).** Atoms ψ, ψ' of the input are
perfectly distinguishable after φ iff `φ_⋄(ψ) ⊥ φ_⋄(ψ')`. Hence the independence
number `α(S_φ)` (one-shot zero-error capacity) is a function of the ⋄-shadow
`(φ_⋄, φ^⋄)` alone: ⋄-equivalent channels (print `eff` 2060) have equal `α`.

**Claim C (⋄ does *not* capture S).** `S_φ` is a subspace; the relation
"`⟨ψ|S_φ|ψ'⟩ = 0`" on pairs of atoms only sees the rank-one part of the
annihilator `S_φ^⊥`. Prediction: there are ⋄-equivalent φ, φ' with `S_φ ≠ S_φ'`
and different Lovász `ϑ`, and — because `α(S^{⊗n})` needs entangled atoms of the
tensor power — with different asymptotic zero-error capacity. That is,
**⋄ is not monoidal in `vNᵒᵖ`**: `(φ⊗id_𝒞)^⋄` is not determined by `φ^⋄`
(it is in `Kl(𝒟)`, where ⋄ is the support relation).

**Claim D (the fix is Weaver).** Weaver's intrinsic quantum relations on 𝒜 are
families of relations on `Proj(𝒜 ⊗̄ 𝒞)`, one per ancilla 𝒞, compatible under
maps of 𝒞 — exactly the data `{(φ ⊗ id_𝒞)_⋄}_𝒞`. Conjecture: the assignment
φ ↦ `{(φ⊗id_𝒞)_⋄}_𝒞` lands in Weaver quantum relations and recovers `S_φ`; i.e.
the ⋄-calculus of thesis B, stabilised by the tensor product of thesis A, *is*
non-commutative graph theory. Complete positivity's "stabilise by an ancilla"
reappearing at the possibilistic level is the surprise.

**Refutation.** Find φ, φ' on M_3 with `φ_⋄ = φ'_⋄`, `φ^⋄ = φ'^⋄` and
`S_φ = S_φ'` forced — e.g. prove `S_φ` is spanned by the rank-one elements of its
own annihilator's annihilator. If that holds in general, Claim C and D collapse
into "⋄ already determines S" (weaker but still a clean theorem).

---

## 3. Ergodic theory of channels: subharmonic projections are ⋄-closed predicates

**Observation.** For a projection p and an endo-channel f: 𝒜 → 𝒜, `p ≤ f(p)`
(Frigerio/Fagnola–Rebolledo "subharmonic") iff `p ≤ ⌊f(p)⌋` iff
`f^⋄(p^⊥) ≤ p^⊥`. So *subharmonic = complement of an `f^⋄`-closed sharp
predicate*, and irreducibility of a quantum Markov map (no nontrivial subharmonic
projection) is a notion available in **any ⋄-effectus**: `f` is ⋄-irreducible iff
the only `s` with `f^⋄(s) ≤ s` are 0, 1. In `Kl(𝒟)`: no proper closed subset of
the support digraph, i.e. strong connectivity. The `f^⋄`-closed predicates form a
complete lattice (f^⋄ is the meet-preserving half of the OMLatGal pair, `eff`
2060VII).

**First result (⋄-period = spectral period).** Define the ⋄-period `d_⋄(f)` as the
largest d such that `1 = s_0 ⊕ … ⊕ s_{d−1}` with sharp s_i and
`f^⋄(s_{i+1}) ≤ s_i` (indices mod d). Claim: for an irreducible normal channel
with a faithful invariant state, `d_⋄(f)` equals the order of the (cyclic)
peripheral spectrum of f.
*Sketch.* Fagnola–Pellicer (2009) produce, from an irreducible map with faithful
invariant state and peripheral eigenvalue `e^{2πi/d}`, a cyclic resolution of the
identity into d projections cyclically permuted by ⌈f(·)⌉ — that is a ⋄-cycle, so
`d_⋄ ≥ d`. Conversely a ⋄-cycle of length d gives `f(Σ_k ζ^k s_k)`'s support
inside `Σ ζ^{k−1} s_{k−1}`; with a faithful invariant state, the standard
Perron–Frobenius argument (`f` restricted to the cycle is a permutation on the
`s_k` up to ⌈·⌉) yields a peripheral eigenvector, so `d_⋄ ≤ d`. In `Kl(𝒟)` both
sides are the gcd of cycle lengths: the classical period.
*What it buys.* An analytic invariant (spectrum on the unit circle) computed from
the possibilistic shadow alone; hence a ⋄-invariant of the endomap, and a
candidate for "symbolic dynamics" of a channel: the ⋄-orbit structure on
`Proj(𝒜)`.

**Refutation.** An irreducible channel with peripheral period d but whose sharp
cyclic resolution is coarser (the ⌈·⌉ of f(s_k) not contained in a single s_{k−1}
because f mixes across the cycle with small weight). Fagnola–Pellicer's
construction should rule this out; if their resolution is only of the *fixed-point
algebra* and not of 1, the ≥ direction fails.

**Secondary (⋄-entropy).** For a sharp partition `P` of 1 and the & of thesis B,
`N_n = #{ (p_0..p_{n−1}) ∈ P^n : p_0 & f(p_1 & f(… p_{n−1})) ≠ 0 }` counts nonzero
"quantum cylinders"; `lim sup (1/n) log N_n` is the topological entropy of the
support subshift in `Kl(𝒟)`. Whether it is interesting in `vNᵒᵖ` (or is always
`log |P|` for non-commuting `P`) is open; not pursued.

---

## 4. Incidence geometry: pure maps are the morphisms of projective geometries, and rigidity is the fundamental theorem

**Claim (finite-dimensional, proved here).** An ncp map φ: M_m → M_n is pure
(print: corner after filter, i.e. `φ = ad_K` for a single K) **iff both** `φ_⋄`
and `φ^⋄` send atoms to atoms-or-0.
*Proof.* `φ_⋄(ψ) = span{K_i ψ}`, `φ^⋄(u) = span{K_i^* u}`. If some K_i has rank ≥ 2,
pointwise parallelism of the K_j to K_i forces `K_j = λ_j K_i`. If all K_i are
rank one, `K_i = |u_i⟩⟨v_i|`, then `φ_⋄` atom-preserving forces the u_i parallel and
`φ^⋄` atom-preserving forces the v_i parallel; again a single Kraus operator.
Converse trivial. One direction alone fails: `φ(y) = ⟨u|y|u⟩ V` with rank V = 2
has `φ_⋄` atom-preserving but `φ^⋄(u) = ⌈V⌉` of rank 2 and is not pure.

**Why it matters.** Join-preserving maps `Proj(H) → Proj(K)` sending atoms to
atoms-or-0 are exactly Faure–Frölicher's *morphisms of projective geometries*
(Stubbe–Van Steirteghem 2007). So: the ⋄-shadow of an arbitrary channel is a
"mixed" incidence morphism, and the pure channels are precisely those whose
shadow is an honest projective-geometry morphism in both directions.

**Rigidity = fundamental theorem.** Print `proc` 1020IX: every pure map is rigid
(determined among ncp maps with the same `f(1)` by `f^⋄`). The fundamental
theorem of projective geometry (Faure–Frölicher form) says a PG morphism of rank
≥ 3 is induced by a semilinear map unique up to scalar. Matching: `f^⋄` fixes K^*
up to a scalar and a linear/antilinear ambiguity; `f(1) = K^*K` fixes the scalar
and the (anti)linearity. Rigidity is therefore a *CP-strengthened* fundamental
theorem — one that still holds in rank 2 (`M_2`), where the geometric statement
is famously false (every bijection of `P(ℂ²)` is a PG isomorphism), because it
quantifies over ncp maps only.

**Conjecture (infinite-dimensional / general vN).** "Pure iff both ⋄-shadows send
atoms to atoms-or-0" in hereditarily atomic algebras (print `proc` 1251, where
atoms exist); for a general vN algebra replace atoms by *the* ⋄-condition
`f_⋄(s) & f_⋄(t) = 0 ⇐ s ⊥ t`? Untested.

**Refutation.** A pure map in the print's sense between M_m ⊕ M_m' and something
whose `φ_⋄` sends an atom to a rank-2 projection — impossible if pure = single
Kraus in every direct-sum block, which the corner/filter description gives.
The infinite-dimensional conjecture is refuted by any pure `ad_K` with K
unbounded-below such that `⌈KψK^*⌉` is not an atom — it always is, so look
instead at non-atomic algebras where the statement is vacuous.

---

## Ranking

1. **§4** — a theorem, proved above in finite dimension, with a conceptual
   payoff (rigidity ↔ fundamental theorem of projective geometry). Cheapest to
   formalise: it is a Kraus-operator lemma.
2. **§1** — a computation, checkable in an afternoon against `dils` 1540, that
   reads the Paschke object as a coupling space; the Monge/Kantorovich ↔
   commutative/non-commutative 𝒫 dichotomy is a nice slogan.
3. **§2** — the most speculative and the most surprising if right: DSW graphs and
   Weaver relations as the ancilla-stabilised ⋄-calculus. Claim A is solid,
   B is easy, C/D need a counterexample search on M_3.
4. **§3** — ⋄-period = spectral period is likely true and likely already
   implicit in Fagnola–Pellicer; the value is only the ⋄-effectus packaging.
