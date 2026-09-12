# Self-dual Hilbert modules as corners of von Neumann algebras

Research note, 2026-09-12. No Lean. Scope: dils.tex parsecs 1430–1650.
Starting point (verified in `Theses/B/Dils/Kaplansky.lean`, "158II through the
linking algebra"): for self-dual `X` over a von Neumann algebra `ℬ`,
`L := ℬᵃ(X ⊕ ℬ)` is a von Neumann algebra with projections `e₁, e₂`,
`ι : ℬ ≅ e₂Le₂` (nmiu), `cor : X ≅ e₁Le₂` (unitary of modules, `⟨S,T⟩ = ι⁻¹(S*T)`),
`ℬᵃ(X) = e₁Le₁`, and the ultranorm uniformity of `X` is the ultrastrong
uniformity of `L` restricted to the corner (`f ↦ f∘ι⁻¹(e₂·e₂)` and
`ω ↦ ω|_{e₂Le₂}` match the seminorms `f(⟨x,x⟩)^{1/2}` and `ω(T*T)^{1/2}` exactly).

Conventions as in the thesis: right modules, `⟨x, yb⟩ = ⟨x,y⟩b`. "Corner of
`(L,e)`" means `(1−e)Le` as a right `eLe`-module with `⟨S,T⟩ = S*T`.

## 0. Summary

The principle: *a self-dual Hilbert `ℬ`-module is a corner `(1−e)Le` of a von
Neumann algebra with `eLe ≅ ℬ`, and conversely every such corner is self dual.*
Inputs that stay as they are: 149V (3 ⇒ 1) and thesis A's ultrastrong /
ultraweak bounded completeness (77I). Everything below is then 2×2 bookkeeping.

| statement | thesis | in `L` | gain |
|---|---|---|---|
| S1 converse | new | corner ⇒ self dual | the theory is the theory of corners |
| S2 completion 150II | 600 lines, transfinite | `X̄ = (1−e)Le` for a concrete `L` | one page; also 152X as a bicommutant |
| S3 ultraweak topology, 158II | — | restriction of `L`'s ultraweak | 149V gets a 5th clause; 158II with ultraweak density |
| S4 ketbras 159IV | ONB + `p_S` argument | `e₁Le₂Le₁` dense in `e₁Le₁` iff `c(e₂)=1` | ONB-free; `ℬᵃ((1−e)Le) = (1−e)c(e)L(1−e)` |
| S5 tensor 164II | ONB-based | `X⊗Y = (e₁⊗e₁)(L_X ⊗̄ L_Y)(e₂⊗e₂)` | also `ℬᵃ(X⊗Y) = ℬᵃ(X) ⊗̄ ℬᵃ(Y)` |
| 157IV | Paschke | corner of a commutant = Arveson RN | repackaging only |

## S1. Converse: every corner is self dual

**Statement.** `L` von Neumann, `e ∈ L` a projection, `ℬ := eLe`. Then
`X := (1−e)Le` is a self-dual Hilbert `ℬ`-module. Hence, for a Hilbert
`ℬ`-module `X`: *self dual ⇔ `X ≅ (1−e)Le` for some `(L,e)` with `eLe ≅ ℬ`*,
and in that case one may take `L = ℬᵃ(X ⊕ ℬ)`.

**Proof.** `X` is a norm-closed right `eLe`-submodule of `L`, `⟨S,T⟩ = S*T ∈ eLe`
is a definite `ℬ`-valued inner product, `‖S‖² = ‖S*S‖`. Its ultranorm
uniformity is the restriction of the ultrastrong uniformity of `L` (seminorm
matching above, which used nothing about the linking algebra). A norm-bounded
ultranorm-Cauchy net in `X` is a bounded ultrastrongly Cauchy net in `L`, so it
converges ultrastrongly in `L` (thesis A: von Neumann algebras are bounded
ultrastrongly complete); `T ↦ (1−e)Te` is ultrastrongly continuous, so the
limit lies in `X`. So `X` is bounded ultranorm complete, and 149V (3 ⇒ 1)
gives self-duality. ∎

Remark (uniqueness of `L`). Left multiplication `L → ℬᵃ(Le)` is nmiu with
kernel `L(1−c(e))` (`c(e)` the central support), and its image contains every
ketbra `|xe⟩⟨ye| = (xey*)·`; by S4 (ONB-free form) these are ultraweakly dense
in `ℬᵃ(Le)`, and an injective normal *-homomorphism has ultraweakly closed
range, so `ℬᵃ(Le) ≅ Lc(e)` and `ℬᵃ((1−e)Le) ≅ (1−e)c(e)L(1−e)`. So the linking
algebra `ℬᵃ(X ⊕ ℬ)` of a corner is `L` itself exactly when `c(e) = 1`, and in
general it is `Lc(e)`.

## S2. The self-dual completion 150II is a corner (best statement)

**Statement.** Let `V` be a right `ℬ`-module with `ℬ`-valued inner product
`[·,·]` (possibly degenerate), `ℬ ⊆ B(H)` a faithful normal representation.
Let `K := V ⊗_ℬ H` (separated completion of `V ⊙ H` for
`⟨v⊗ξ, w⊗η⟩ := ⟨ξ, [v,w]η⟩`), let `ℬ'` act on `K ⊕ H` by `(1⊗c') ⊕ c'`, and
`L := (ℬ'_diag)'`, `e :=` projection onto `H`. Then
- `eLe = ℬ'' = ℬ` (bicommutant), and `η : V → (1−e)Le`, `η(v)ξ := v ⊗ ξ`, is
  `ℬ`-linear with `η(v)*η(w) = [v,w]`;
- `X̄ := (1−e)Le` is self dual (S1) and `η(V)` is ultranorm dense in it;
- `ℬᵃ(X̄) = (1−e)L(1−e) = (1 ⊗ ℬ')' ⊆ B(K)`.
So `(X̄, η)` is the self-dual completion of 150II, and 152X for `X̄`
(hence for every self-dual `X`, taking `V = X`) is the bicommutant theorem.

**Proof.** Positivity of the form on `V ⊙ H`: `Σ_{ij} b_i*[v_i,v_j]b_j =
[Σ v_i b_i, Σ v_j b_j] ≥ 0` for all `b_i ∈ ℬ`, so `([v_i,v_j])_{ij} ≥ 0` in
`M_n(ℬ)`, so `Σ⟨ξ_i,[v_i,v_j]ξ_j⟩ ≥ 0`. `η(v)` intertwines `ℬ'`:
`η(v)c'ξ = v⊗c'ξ = (1⊗c')η(v)ξ`, and
`⟨ξ, η(v)*η(w)η⟩ = ⟨v⊗ξ, w⊗η⟩ = ⟨ξ,[v,w]η⟩`.
Density: let `X₀ := ` ultrastrong closure of `η(V)` in `(1−e)Le` (a corner
submodule; bounded ultranorm complete as in S1, hence self dual by 149V). For
`T ∈ (1−e)Le` and `y ∈ X₀`, `τ(y) := T*η̃(y) ∈ (ℬ')' = ℬ` (writing `η̃(y)ξ := y⊗ξ`,
i.e. `η̃(y) = y` as an operator `H → K`) is a bounded `ℬ`-linear map `X₀ → ℬ`;
self-duality gives `x ∈ X₀` with `T*y = x*y` for all `y ∈ X₀`, i.e.
`(T−x)*(y⊗ξ) = 0` for all `y ∈ X₀ ⊇ η(V)`, `ξ ∈ H`; these span a dense subspace
of `K`, so `T = x ∈ X₀`. Hence `X̄ = X₀` and `η(V)` is ultrastrongly (= ultranorm)
dense. Adjointables: `ℬᵃ(X̄) ⊆ (1⊗ℬ')'` is clear; conversely `S ∈ (1⊗ℬ')'`
sends `x ∈ X̄ = (1−e)Le` to `Sx ∈ (1−e)Le`, and `S(xb) = (Sx)b`,
`⟨Sx,y⟩ = x*S*y = ⟨x,S*y⟩`, so `S ∈ ℬᵃ(X̄)`. ∎

Consequences. (i) 151II/163II universality: a bounded module map `T : V → Y`,
`Y` self dual, is uniformly ultranorm continuous (147I); by 158II in the form
S3 below get for `x ∈ X̄` a *bounded* net in `η(V)` converging to `x`, its
image is bounded ultranorm Cauchy in `Y`, converges by 149V (1 ⇒ 3); this
defines `T̂`. (ii) The abstract and concrete linking algebras agree:
`ℬᵃ(X ⊕ ℬ) ≅ L` entrywise (`e₁Le₁ = ℬᵃ(X)`, `e₁Le₂ = X`, `e₂Le₂ = ℬ`).
(iii) The thesis proof of 150II (lines 2632–3257 of dils.tex, an induction over
ordinals) is replaced by the above, at the price of assuming 149V (3 ⇒ 1),
which the thesis proves before 150II anyway. Paschke's own proof of 3.2 is
different again (dual Banach modules).

## S3. The module ultraweak topology; 149V(5); 158II with ultraweak density

**Definition.** For self-dual `X` the *ultraweak* uniformity is the restriction
of the ultraweak uniformity of `L`. Equivalently (via vector functionals
`⟨y⊗ξ, x⊗η⟩ = f(⟨y,x⟩)`, `f = ⟨ξ,·η⟩`, and norm limits): it is `σ(X, X_♭)` with
`X_♭ :=` closed span of `{f(⟨y,·⟩) ; f ∈ ℬ_*, y ∈ X}` — Paschke's weak*
topology. `X = e₁Le₂` is ultraweakly closed in `L = (L_*)^*`, so `X` is a dual
Banach space with unit ball ultraweakly compact (Paschke's theorem, free).

**Statement.** (a) Norm-bounded ultraweakly Cauchy nets in `X` converge
(77I in `L`, compress). (b) 149V gets a fifth equivalent clause:
*(5) every norm-bounded ultraweakly Cauchy net converges.* (c) For convex
`C ⊆ X`, ultranorm closure = ultraweak closure (Mazur: the dual of `(L,
ultrastrong)` is `L_*`; an ultranorm-continuous functional on the corner
extends by Hahn–Banach). (d) 158II holds for self-dual `X` with "`D`
ultranorm dense" weakened to "`D` ultraweakly dense"; in particular an
`𝒜`-submodule `D` with `⟨D,D⟩ ⊆ 𝒜` is ultraweakly dense iff ultranorm dense.

**Proof.** (b): (5 ⇒ 3) — if `x_α` is bounded ultranorm Cauchy it is
ultraweakly Cauchy, so `x_α → x` ultraweakly; then
`f(⟨x_α−x, x_α−x⟩) = lim_β f(⟨x_α−x, x_α−x_β⟩) ≤ ‖x_α−x‖_f · liminf_β ‖x_α−x_β‖_f`
(137III Cauchy–Schwarz for `f∘⟨·,·⟩`), so `‖x_α−x‖_f ≤ liminf_β ‖x_α−x_β‖_f → 0`.
(3 ⇒ 5) is (a) plus 149V. (d): the Lean proof puts `D` in the *-subalgebra
`𝒮 ⊆ L` of operators preserving `cl(D) ⊕ 𝒜`; the only use of density is
"`cor(x)` lies in the ultrastrong closure of `𝒮`", and for the convex set `𝒮`
that closure equals the ultraweak closure, which contains `cor(D)`'s ultraweak
closure `⊇ cor(X)`. 74IV then gives the bounded net; compress and rescale as
in Lean. ∎ (For non-self-dual `X`, 158II follows from the self-dual case
through S2, as the ultranorm uniformity of `X` is the restriction of `X̄`'s.)

## S4. Ketbras 159IV: density of `e₁Le₂Le₁`

**Statement.** In `L = ℬᵃ(X ⊕ ℬ)`: `|x⟩⟨y| = cor(x)·cor(y)*`, so
`span{|x⟩⟨y|} = e₁ (L e₂ L) e₁`. The ultraweak closure of the ideal `Le₂L` is
`Lc(e₂)`, and `c(e₂) = 1` in the linking algebra. Hence *the span of all
ketbras is ultraweakly dense in `ℬᵃ(X)`*, with no orthonormal basis; the
ONB-indexed 159IV follows since `|x⟩⟨y|` is an ultraweak limit of finite sums
`|Σe_i⟨e_i,x⟩⟩⟨Σe_j⟨e_j,y⟩|` (159VIII).

**Proof.** `c(e₂) = 1`: a central projection `q ≤ 1−c(e₂) ≤ e₁` satisfies
`q·cor(x) = q e₁ cor(x) e₂ = cor(x) q e₂ = 0`, i.e. `qx = 0` for all `x ∈ X`, so
`q = 0`. Ultraweakly closed two-sided ideals of a von Neumann algebra are
`Lz` with `z` central (classical; check whether thesis A has it — if not,
this is the one imported fact), and the closure of `Le₂L` is the smallest such
containing `e₂`, namely `Lc(e₂)`. ∎ This is the fact used in the S1 remark.

## S5. Tensor products 164II as corners of `L_X ⊗̄ L_Y`

**Statement.** `X` self dual over `𝒜`, `Y` over `ℬ`, `L_X, L_Y` the linking
algebras, `M := L_X ⊗̄ L_Y` (spatial von Neumann tensor product, thesis A).
Then `(e₂⊗e₂)M(e₂⊗e₂) = 𝒜 ⊗̄ ℬ`, and
`X ⊗ Y ≅ (e₁⊗e₁) M (e₂⊗e₂)` with `x ⊗̂ y = cor(x) ⊗ cor(y)`;
moreover `ℬᵃ(X ⊗ Y) = (e₁⊗e₁)M(e₁⊗e₁) = ℬᵃ(X) ⊗̄ ℬᵃ(Y)`.

**Proof.** Corners of tensor products are tensor products of corners
(`(p⊗q)(M⊗̄N)(p⊗q) = pMp ⊗̄ qNq`, standard). The corner `Z := (e₁⊗e₁)M(e₂⊗e₂)`
is self dual over `𝒜⊗̄ℬ` by S1; `η(x⊗y) := cor(x)⊗cor(y)` preserves inner
products (`(cor x ⊗ cor y)*(cor x' ⊗ cor y') = ⟨x,x'⟩⊗⟨y,y'⟩`) and is
`𝒜⊙ℬ`-linear; elementary tensors are ultraweakly dense in `M`, compress, so
`η(X ⊙ Y)` is ultraweakly dense in `Z`, hence ultranorm dense by S3(c) (it is a
subspace). Universality then is 163II. `ℬᵃ(Z) = (e₁⊗e₁)c(e₂⊗e₂)M(e₁⊗e₁)` by
the S1 remark, and `c(e₂⊗e₂) = c(e₂)⊗c(e₂) = 1` (`Z(M⊗̄N) = Z(M)⊗̄Z(N)`,
Tomita's commutation theorem — classical, not in thesis A as far as I know;
without it one still gets `ℬᵃ(X⊗Y) ⊇ ℬᵃ(X)⊗̄ℬᵃ(Y)` with dense ketbras,
which is 164II(2b)). ∎ 164II(2a), `e_i ⊗̂ d_j` an ONB, is a direct check.

## 157IV: the corner of a commutant (repackaging only)

With `ρ : 𝒜 → e₁Le₁`, `ξ = 1⊗1`, `h(T) = ι⁻¹(cor(ξ)* T cor(ξ))`, and
`M_ρ := ρ(𝒜) ⊕ ℂe₂ ⊆ L`, one has `M_ρ' ∩ L = ρ(𝒜)'_{ℬᵃ(X)} ⊕ ℬ`, so
`[0,1]_{ρ(𝒜)'} = e₁[0,1]_{M_ρ'}e₁` and `φ_t = ι⁻¹(cor(ξ)* t ρ(·) cor(ξ))`.
Through the concrete `L` of S2, `X ⊗_ℬ H = 𝒜 ⊗_φ H` is the Stinespring space of
`𝒜 → ℬ ⊆ B(H)` and `ρ(𝒜)' ∩ ℬᵃ(X) = (ρ(𝒜) ∪ (1⊗ℬ'))'`; so 157IV is Arveson's
Radon–Nikodym theorem for the Stinespring dilation plus the observation that
the RN derivative `t` of a `ψ ≤ φ` with values in `ℬ` commutes with `1⊗ℬ'`
(conjugate `t` by a unitary of `1⊗ℬ'`; `ψ_t` is unchanged, uniqueness). The
proof is not shorter than the thesis's (152V does the work either way); the
gain is identification, not simplification.

## What does not become easier

152X for `X ⊕ ℬ` is an input to the abstract linking algebra (circular
otherwise); S2's concrete `L` breaks the circle but needs the interior tensor
product `X ⊗_ℬ H`. 149V (3 ⇒ 1) (Zorn over orthonormal families) is the
irreducible module-theoretic input; nothing in the corner picture replaces it.
162IV (classification over factors) is the comparison theory of projections in
`L`, unchanged.

## Suggested order for a rewrite of parsecs 1490–1650

149V (as is) → S2 (concrete `L`; 150II, 152X, 151II/163II in one go) →
S1 (corners) → S3 (ultraweak topology; 158II) → S4 (159IV) → S5 (164II) →
157IV cited as Arveson RN. Imported classical facts to check against thesis A:
bounded ultrastrong/ultraweak completeness (77I), 74IV, "ultraweakly closed
ideals are `Lz`", ultraweak = ultrastrong closure of convex sets, corners and
centres of `⊗̄`.
