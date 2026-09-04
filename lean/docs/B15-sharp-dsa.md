# B15 addendum: which sharp maps are ⋄-self-adjoint?

**Claim under test.** A sharp endomap `f : X → X` in a †-effectus is
⋄-self-adjoint iff `IM f = ⌈1 ∘ f⌉` and the induced iso `ϑ` of that corner is an
involution, via `f = π_i ∘ ϑ ∘ ζ_s`, `f^⋄ = π_s ∘ ϑ⁻¹ ∘ ζ_i`; in `vNᵒᵖ` this is
`ad_v` with `v = v*` a partial isometry of central support; hence every such map
is pure.

## Verdict: the conclusion is right, two of the four steps are not.

The **classification is correct** and the **purity corollary stands** — but
(i) the factorization is *not* a citable property of sharp maps, it is part of
what has to be proved; (ii) `f^⋄ = π_s ∘ ϑ⁻¹ ∘ ζ_i` is a type error (that map is
`f^†`), and the ⋄-condition it yields is weaker than `f = f^†`; and (iii) `ad_v`
catches only the **inner** case — the general answer is an involutive
*automorphism* of a central corner, which need not be inner.

## (i) Sharp ⇏ pure: the factorization is not available up front

`standard-form-map` (**212III**, eff.tex:5102) factors *every* map as
`f = π_{IM f} ∘ g ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f}` with `g` total and **faithful**;
`g` is an *isomorphism* only under the hypothesis that `f` is **pure**
(clause 1). Sharpness gives the two cosmetic simplifications — `1 ∘ f` is sharp
(apply sharpness to `1`), so `asrt_{1∘f}` is absorbed by `ζ_s ∘ asrt_s = ζ_s` —
but nothing about `g`. And sharp maps are genuinely not pure in general: in
`vNᵒᵖ` sharp = normal *-homomorphism (**210III** `exa-sharp-vn`), and

* `φ : ℂ⊕M₂ → ℂ⊕M₂`, `φ(λ,a) = (λ, λ1₂)` — normal, unital, multiplicative;
  `⌈φ⌉ = (1,0)` so `⌈φ⌉𝒜 = ℂ`, while `φ(1)𝒜φ(1) = 𝒜`, and `ℂ ≇ ℂ⊕M₂`;
* `φ(a) = V₁aV₁* + V₂aV₂*` on `B(ℓ²)` with `V₁,V₂` isometries, `ΣVᵢVᵢ* = 1`
  (Cuntz): unital, injective, normal, multiplicative, **not** surjective.

Both are sharp and impure, so "sharp ⟹ quotient∘iso∘comprehension" is false.
The iso must be *derived* from ⋄-self-adjointness (below), and neither example is
⋄-self-adjoint — consistent.

## (ii) The three dagger lemmas give `f^†`, not `f^⋄`

`f^⋄ : SPred X → SPred X` is a map on predicates; `π_s ∘ ϑ⁻¹ ∘ ζ_i` is a map in
the category. What the lemmas give is, for `f = π_i ∘ ϑ ∘ ζ_s`,

    f^†  =  ζ_s^† ∘ ϑ^† ∘ π_i^†  =  π_s ∘ ϑ⁻¹ ∘ ζ_i,

by **216VII** `dagger-of-zeta` (`ζ_s^† = π_s`), its dual (`π_s^† = ζ_s`) and
**216IX** `dagger-of-iso` (`ϑ^† = ϑ⁻¹`) — in the tree `dagger_of_zeta`,
`dagger_of_compr` and `dagger_of_iso` (`Theses/B/Eff/Dagger.lean:305, 384, 400`).
This step of the claim is sound once restated for `†`.

But `f` is ⋄-adjoint to `f^†`, i.e. `f^⋄ = (f^†)_⋄`, so

    f ⋄-self-adjoint  ⟺  (f^†)_⋄ = f_⋄  ⟺  f^† is ⋄-**equivalent** to f,

which is strictly weaker than `f = f^†` in general (⋄-equivalence is not
rigid — cf. the impure witnesses of `B15-dsa-match.md`). Equality is recovered
only *because* `f` is sharp: a sharp `φ` sends projections to projections, so
`f^⋄ = φ|proj` determines `f` by normality, and two ⋄-equivalent sharp maps
coincide. The claim's argument silently uses this.

## The one step that is free: image = support

For *any* map, `f^⋄(1) = ⌈1 ∘ f⌉` and `f_⋄(1) = IM(f ∘ π_1) = IM f` (`π_1` is
iso). So ⋄-self-adjointness gives `IM f = ⌈1 ∘ f⌉` by evaluating at `1` —
no sharpness needed. In `vNᵒᵖ`: `⌈φ⌉ = φ(1)`.

## (iii) The `vNᵒᵖ` characterization

Use the contraposed form of ⋄-self-adjointness (`B15-dsa-match.md`): for
projections `s,t`, `⌈φ(t)⌉ ≤ s^⊥ ⟺ ⌈φ(s)⌉ ≤ t^⊥`. For a *-hom `φ(t)` is already
a projection, so the condition is

    (∗)   φ(t)s = 0  ⟺  φ(s)t = 0     for all projections s,t.

Let `p = φ(1)` (a projection: `φ(1) = φ(1)² = φ(1)*`) and `z = ⌈φ⌉`, which is
**central** because `ker φ` is a weak-* closed two-sided ideal.

* `t = z^⊥` kills the left side, so `φ(s) ≤ z` for all `s`, i.e. `p ≤ z`.
* `s = p^⊥` kills the left side (`φ(t) ≤ p`), so `φ(p^⊥) = 0`, i.e. `z ≤ p`.
* Hence `p = z` is central and `φ(a) = ϑ(za)` for `ϑ := φ|_{z𝒜}`, a normal,
  unital, injective *-endomorphism of `z𝒜`.
* `s := ϑ(t)^⊥` in (∗) gives `ϑ(ϑ(t)^⊥)t = 0`, i.e. `ϑ²(t)^⊥ t = 0`, i.e.
  `t ≤ ϑ²(t)`; applied to `t^⊥` and complemented, `ϑ²(t) ≤ t`. So **`ϑ² = id`**
  — in particular `ϑ` is *surjective*, an automorphism.
* Conversely `ϑ² = id` on a central corner gives (∗) by applying `ϑ`.

**Theorem (`vNᵒᵖ`).** For ncpsu `φ : 𝒜 → 𝒜`: `φ` is a sharp ⋄-self-adjoint map
iff there are a central projection `z` and an involutive *-automorphism `ϑ` of
`z𝒜` with `φ(a) = ϑ(za)`. Then `φ(1) = ⌈φ⌉ = z` and, in the effectus,
`f = π_z ∘ ϑ ∘ ζ_z` with `f^† = π_z ∘ ϑ⁻¹ ∘ ζ_z = f`.

### `ad_v` is only the inner case

`ad_v` (`v = v*` a partial isometry, `q := v² = v*v = vv*`) is multiplicative iff
`q` is central:

    ad_v(x)ad_v(y) − ad_v(xy) = v x v v y v − v x y v = − v x (1−q) y v,

and conjugating by `v` (using `vq = v`, `v² = q`) this vanishes for all `x,y` iff
`q x (1−q) y q = 0` for all `x,y`; taking `y = x*` gives `(qx(1−q))(qx(1−q))* = 0`,
so `q𝒜(1−q) = 0`, i.e. `q` central — and conversely. So **centrality is forced by
multiplicativity**, exactly as the claim guessed; then `φ(1) = ⌈φ⌉ = q` and
`ad_v ∘ ad_v = id` on `q𝒜`, so every such `ad_v` is sharp and ⋄-self-adjoint.
Special cases: `ad_p` for central `p` (`ϑ = id`) and `ad_u` for a symmetry `u`.

**But not every case is `ad_v`:** the swap `ϑ(λ,μ) = (μ,λ)` on `𝒜 = ℂ⊕ℂ` is an
involutive automorphism (hence sharp ⋄-self-adjoint), while every `ad_v` on `ℂ⊕ℂ`
is diagonal, `(λ,μ) ↦ (|v₁|²λ, |v₂|²μ)`. Outer involutions of the hyperfinite
II₁ factor give infinite-dimensional witnesses. **Corrected statement:** `v` a
self-adjoint partial isometry with central `v²` is the *inner* subfamily; the
class is "involutive automorphism of a central corner".

## (iv) No impure witness — the purity corollary survives

`φ(a) = ϑ(za)` factors as `𝒜 --(a↦za)--> z𝒜 --ϑ--> z𝒜 ↪ 𝒜`, i.e.
`f = π_z ∘ ϑ ∘ ζ_z` in the effectus: comprehension after (iso after quotient),
hence **pure**. So in `vNᵒᵖ` there is no sharp ⋄-self-adjoint map that is impure,
and on **sharp** maps proc.tex's ⋄-self-adjoint (pure + contraposed) and
eff.tex's **206II** ⋄-self-adjoint (`f^⋄ = f_⋄`) do coincide. This does not
extend past sharp maps: `ad_{B₁} + ad_{B₂}` (`B15-dsa-match.md`) is
eff-⋄-self-adjoint, impure, and not sharp.

Note the purity argument is `vN`-specific: it runs on the centrality of `⌈φ⌉`
for a *-homomorphism. Abstractly one gets only that the standard-form `g` is
total, faithful and ⋄-self-adjoint; "such a `g` is an iso" is the missing
general lemma.
