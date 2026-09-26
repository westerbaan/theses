# Review: REC 92 under separation by predicates (flag 18)

**Verdict: FALSE WITHOUT IT.** The printed REC 92 (`prop:predsep-splits`,
short.tex:1643) is false in the predicate-separated case, and not only its proof.
Below is a predicate-separated effectus with images and compatible filters and
comprehensions, and a non-trivial idempotent scalar `s`, where `s∘1_A` is not
sharp for some `A`, and `C` is not equivalent to any product of two non-trivial
effectuses. The state-separated case (`rec92_states`) and the Lean
`rec92_predicates`, which assumes `s∘1`, `s^⊥∘1` sharp, stand.

(a) Can sharpness be derived? In a *sequential* effectus, yes, but trivially:
sequential effectuses are separated by states by definition (Def.
`def:sequential-effectus`), and there sharp ⟺ idempotent (`prop:idempotent-is-sharp`),
with `(s∘1)&(s∘1) = s∘(1∘asrt_{s∘1}) = s∘s∘1 = s∘1`. So the question only matters
for REC 92's bare effectus hypotheses, and there it fails.

## The counterexample `C` ("linked points")

Objects: triples `X = (a, l, r)` of finite sets. Write `X₁ = a ⊔ l` and
`X₂ = a ⊔ r`, so an `a`-point is present in both components, an `l`-point only
in the first and an `r`-point only in the second.
Maps `f : X → Y`: pairs of partial functions `f₁ : X₁ ⇀ Y₁`, `f₂ : X₂ ⇀ Y₂` such that
for every `y ∈ a_Y`, `f₁⁻¹(y) = f₂⁻¹(y) ⊆ a_X`. In words, only linked points reach
linked points, and they do so in both components at once. Equivalently, `C` is the
subcategory of `Pfn × Pfn` of pairs whose preimage map preserves
`θ_X = {(W,W) : W ⊆ a_X} ⊆ 2^{X₁} × 2^{X₂}`, so composition is closed.

* **finPAC.** Coproducts are componentwise, `(a⊔a', l⊔l', r⊔r')`, and cotuples satisfy
  the constraint. The zero object is `(∅,∅,∅)`. `f ⊥ g` iff the domains are
  disjoint in each component, and the sum is the union. The bound
  `X → Y+Y` of a summable pair is a `C`-map, and so are `▷ᵢ`. The compatible-sum
  and untying axioms hold because they hold in `Pfn × Pfn`.
* **Unit** `I = (∅, 1, 1)`, so `I = L + R` with `L = (∅,1,∅)` and
  `R = (∅,∅,1)`. Maps into `I` meet no constraint, so
  `Pred(X) = 2^{X₁} × 2^{X₂}`, a Boolean effect algebra. `1∘f = 0 ⇒ f = 0` holds, and
  `1∘f ⊥ 1∘g ⇒ f ⊥ g` holds by the bound above. So `C` is an effectus.
* **Scalars** are `M = {0,1}²`, with `s = (1,0)` idempotent and non-trivial.
  `s∘p = (p₁, ∅)`.
* **Separated by predicates.** Partial functions are determined by the preimages
  of singletons, and every pair of subsets is a predicate. `C` is **not**
  separated by states: `A := (1,∅,∅)` (one linked point) has only the zero
  substate, since `l`- and `r`-points of `I` cannot reach `a_A`, yet
  `id_A ≠ 0`.
* **Images:** `im f = (ran f₁, ran f₂)`.
* **Comprehension** of `p = (P₁,P₂)` on `(a,l,r)`: take
  `(a∩P₁∩P₂, l∩P₁, r∩P₂)` with the inclusion. A map landing in `P` can hit a
  linked point `x` only through both components, so it needs `x ∈ P₁ ∩ P₂`.
  Hence `⌊p⌋ = ((a∩P₁∩P₂) ⊔ (l∩P₁), (a∩P₁∩P₂) ⊔ (r∩P₂))`.
* **Filter** of `p`: take `(a∩P₁∩P₂, (l∩P₁) ⊔ (a∩P₁∖P₂), (r∩P₂) ⊔ (a∩P₂∖P₁))`
  with the partial identity. A linked point in only one of the `Pᵢ` becomes
  unlinked, which keeps `ξ` a `C`-map. Universality: if `dom gᵢ ⊆ Pᵢ`, then
  `g⁻¹(y) ⊆ a∩P₁∩P₂` for every linked `y`.
* **Compatible.** A sharp `p` satisfies `P₁∩a = P₂∩a`. Then the filter and
  comprehension objects coincide and `ξ^p ∘ π_p = id`.

**Failure.** On `A = (1,∅,∅)` we have `s∘1_A = (1,∅)`. The maps `f` into `A` with
`s∘1∘f = 1∘f` have `dom f₂ = ∅`, which forces `f₁⁻¹(*) = f₂⁻¹(*) = ∅`, so `f = 0`.
The comprehension is therefore the zero object, and
`⌊s∘1_A⌋ = 0 ≠ s∘1_A`: the predicate is not sharp. The same holds for
`s^⊥∘1_A = (∅,1)`. Put differently, `s·id_A = (id, 0)` is not a map, because it
breaks the link. So `asrt_{s∘1_A}`, as used in the printed proof, does not exist.

**The statement fails.** Suppose `C ≃ D₁ × D₂` as effectuses (unit to unit), with
both factors non-trivial. Then `M ≅ M₁ × M₂` with `M₁ = M₂ = {0,1}`, and the
idempotent `(1,0)` of the product corresponds to `s` or `s^⊥`. In `D₁ × D₂`,
`(1,0)∘1_{(A₁,A₂)} = (1,0)` is the image of `(id,0)`, so it is sharp. Sharpness is
invariant under equivalence, because images, zero maps and scalar action are
categorical. That contradicts the Failure paragraph. So `C` is indecomposable
although its scalars are `{0,1}²`.

## Relation to the other REC points
* REC 91 (monoidal) is untouched: `C` has no monoidal structure making
  `s ⊗ id` exist. That is exactly what the `s · id` argument needs.
* The state-separated case is fine: `isSharp_of_states` uses states
  `ω ∘ s` factoring through `π`. In `C` the object `A` is stateless, which is
  the REC 89 `(I,s)` phenomenon made into an honest object.
* Downstream use (REC 93/95, `dcSplitting`) is state-separated only, so no
  later result is affected.

## Suggested ERRATA entry (replaces the current REC 92 entry)
> **REC 92** (`prop:predsep-splits`, short.tex:1643, Proposition) — **false as
> printed for separation by predicates**; true for separation by states. The
> proof takes `asrt_{s∘1}`, which needs `s∘1` sharp. Under state separation it
> is (`⌊s∘1⌋` agrees with `s∘1` on states, since `ω∘s` factors through `π_{s∘1}`).
> Under predicate separation it need not be. Counterexample: in the subcategory
> of `Pfn × Pfn` on "linked/left/right points", every predicate is a pair of
> subsets and `s = (1,0)` is a scalar. For one linked point `A`,
> `s·id_A = (id,0)` is not a map. `s∘1_A` has comprehension `0` and so is not
> sharp. The effectus is predicate-separated, with images and compatible
> filters and comprehensions, but it is not a product of two non-trivial
> effectuses (in a product, `s∘1` is always sharp). Correct statement: add the
> hypothesis "`s∘1_A` and `s^⊥∘1_A` are sharp for all `A`". This is implied by
> state separation or by a monoidal structure (REC 91). Lean:
> `rec92_states`, `rec92_predicates` (with the hypothesis), `isSharp_of_states`;
> the counterexample is not yet formalised.

## Handover
The Lean refutation is finite and decidable, much like `BoolMat` (objects are triples
of `Fintype`s). Get a break-it review first (finPAC axioms of `C`; whether an
equivalence preserves the unit and the scalar action).
