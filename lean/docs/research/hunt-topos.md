# Hunt: effectuses versus toposes and sheaves

Wild-hypothesis hunt, 2026-09-12, no Lean. Sources: eff.tex 2030 (sharp = image),
2060 (⋄-effectus, `f_⋄ ⊣ f^□`), Cho's `diamond-oml` (SPred X is an OML), 192 (`Kl(𝒟_M)`),
proc 127III (duplicable ⟺ `ℓ^∞(X)`); `new-base.md` Prop 1.1/Cor 1.4 (`cC*ᵒᵖ = Kl(Radon)`,
quotient `β(coz a)`, hyperstonean coreflection) and `new-categorical-probability.md` Thm 3.2
(Giry has no images) are *assumed*, not repeated. Every "Thm" below is a hand argument.

Four conjectures, one lemma. Verdicts: C1 KILLED, C2 KILLED (sharpened form survives),
C3 KILLED, C4 KILLED as stated, Lemma L SURVIVED (proved).

## C1. Bohrification reconstructs the ⋄-effectus `vNᵒᵖ` at `𝒜`

**Conjecture.** With `𝒞(𝒜)` the poset of commutative vN subalgebras and `𝒯(𝒜) = [𝒞(𝒜), Set]`,
the internal effectus `CvNᵒᵖ` of `𝒯(𝒜)` at the Bohrified object `𝒜̲ : C ↦ C` recovers `Pred 𝒜`,
`SPred 𝒜` with its OML structure, quotients and comprehension of `vNᵒᵖ` at `𝒜`.

**KILLED, three ways, sharpest first.**

1. *Predicates are not locally commutative.* Internal predicates on `𝒜̲` form the copresheaf
   `C ↦ [0,1]_C`; the only external object this determines is `colim_C [0,1]_C` in posets
   (and in PCMs): elements are all effects (every effect lies in a masa), but `a ≤ b` and
   `a ⊥ b` are recorded only when `a, b` lie in a common `C`. In `M_2` take rank-one
   `p ≠ q`, `a = 0.6·p`, `b = (1+q)/2`: `b − a ≥ 0` (det `1/2 − 3·0.6/4 > 0`), so `a ≤ b`
   in `Pred M_2`, but no commutative subalgebra contains both. So `Pred M_2` is not the colimit
   of its commutative pieces even as a poset. Since ⌈·⌉, `f^⋄`, ⊑ are all defined through ≤,
   nothing built on predicates is recovered. This kills C1 already at `M_2`, where
   Kochen–Specker is silent (`Σ` *has* global points for `M_2`: pick one bit per masa).
2. *Sharp predicates are recovered only as an orthoposet.* `SPred 𝒜 = Proj 𝒜` **is** the
   colimit of its blocks `Proj C` as an orthoposet (in any OML `s ≤ t` forces `s, t` to
   commute, hence to share a block; orthocomplement likewise), so the *order and ⊥ of
   `SPred`* are locally Boolean. The lattice operations are not: internally, at every stage,
   `∀s t u. s ∧ (t ∨ u) = (s∧t) ∨ (s∧u)` is forced (Kripke–Joyal over inclusions of Boolean
   algebras), while in `Proj M_3` it fails for three rank-one projections. Cho's
   `s ∨ t = im[π_s, π_t]` is exactly the operation the Bohr topos cannot see: internal
   comprehension of `p ∈ C` is `pCp` at stage `C`, so the internal `[π_s, π_t]` for
   non-commuting `s, t` never exists at any stage.
3. *The object itself is not recovered, and the failure is effectus-visible.* Döring–Harding
   and Hamhalter: `𝒞(𝒜) ≅ 𝒞(ℬ)` iff `𝒜 ≅ ℬ` as Jordan algebras (no `I_2` summand). With
   Connes' `II_1` factor `𝒜 ≇ 𝒜ᵒᵖ`, the objects `𝒜 ⊕ 𝒜` and `𝒜 ⊕ 𝒜ᵒᵖ` have equivalent Bohr
   toposes, yet the effectus-definable property "`X ≅ Y ⊕ Y` for some `Y`" separates them
   (a splitting of `𝒜 ⊕ 𝒜ᵒᵖ` into two isomorphic summands would give `𝒜 ≅ 𝒜ᵒᵖ`). So the Bohr
   topos is strictly coarser than the effectus, even up to automorphisms of `vNᵒᵖ`.

*Residue worth keeping.* "Locally Boolean" is a theorem about `SPred`, not about `Pred`. Any
Bohr-style reconstruction of a ⋄-effectus must therefore start from images/⌈·⌉ on
non-commuting effects, i.e. from the ⋄-adjunction `f_⋄ ⊣ f^□`, which is not a colimit of
Boolean data. (Döring–Isham's daseinisation is the known ∨-only embedding of `Proj 𝒜` into a
Heyting algebra; it is not a lattice map and does not change the verdict.)

## C2. `Kl(𝒟)` internal to `Sh(X)` is the ⋄-effectus of continuous stochastic families

**Setting (checked).** Internal `𝒟` uses Kuratowski-finite support and the Dedekind reals,
so a map `ΔY → 𝒟ΔZ` in the internal Kleisli category is a *locally finite* continuous family
`x ↦ f_x ∈ 𝒟(Z)` (coefficients continuous in `x`, finitely many nonzero near each `x`);
predicates on `ΔY` are continuous `X × Y_disc → [0,1]`; scalars are `C(X, [0,1])`. So it is
*not* "Markov kernels over `X`" (`Z = ℕ` with a geometric family is excluded), but a
well-defined effectus; quotients (`{p > 0}` is open, division by `p` is internal there) and
comprehension (`{p = 1}` is a subsheaf) go through constructively.

**Conjecture.** It is a ⋄-effectus (has images) for every `X`.

**KILLED.** Images are the least *sharp* predicate above the support, and sharp predicates
on `ΔY` are 0/1-valued continuous functions, i.e. clopen subsets of `X × Y`. Take
`X = [0,1]`, `Y = Z = 1`, partial map `f(x) = max(0, ½ − x)·|∗⟩`. Any `s` with
`s ∘ f = 1 ∘ f` is `1` on `[0, ½)`, hence on `[0, ½]`; the set of continuous such `s` has
infimum `1_{[0,½]}`, not continuous: **no image**. This is Giry's failure (no least support)
reappearing topologically: the support is open but its closure is not.

**Sharpened form (SURVIVED the tests I ran).** *`Kl(𝒟)` internal to `Sh(X)` has images
for maps out of `Δ1` iff every cozero set of `X` has open closure, i.e. iff `X` is basically
disconnected (Gillman–Jerison 1H; equivalently `C(X)` is σ-Dedekind complete).* Proof of ⇐:
support `S = {f > 0}` is cozero, `cl S` clopen, `1_{cl S}` is continuous, satisfies
`s ∘ f = 1 ∘ f`, and is below every continuous `s` that is `1` on `S`. Proof of ⇒: a cozero
set `S = {g > 0}` with non-open closure gives `f = g·|∗⟩` without image, as above. Then `s^⊥`
of a clopen is clopen, so the ⋄-axiom holds. For general sheaves the same criterion applies
on the étale space, which is locally `X`; not checked whether "basically disconnected" is
local. Corollaries: for metrizable `X` the internal `Kl(𝒟)` is a ⋄-effectus iff `X` is
discrete (metrizable basically-disconnected spaces are discrete), i.e. iff `Sh(X) = Set^X`
and the effectus is a product of copies of `Kl(𝒟)`. So the only *connected* base over which
"internal `Kl(𝒟)`" has supports is a point.

## C3. Ozawa's transfer principle hands us effectus theorems for free

**Conjecture.** The fibration `SPred → C` of a ⋄-effectus, with OML fibres, is the subobject
fibration of an "orthomodular-valued set" universe `V^{(SPred X)}` (Takeuti/Ozawa), and
Ozawa's Δ₀-transfer (bounded ZFC theorems hold with truth value ≥ the commutator of the
parameters) yields the ⋄-effectus theorems about `X` from their classical versions.

**KILLED.**

1. `V^{(Q)}` is not a topos and not a model of intuitionistic set theory: for non-Boolean `Q`
   substitution of equals fails and truth values of `=` are not transitive; Ozawa's theorem
   is exactly that theorems survive *modulo the commutator*, which in a factor is `0` for any
   non-commuting pair. So the transfer says nothing off the commutative part; it is
   Bohrification (C1) in Boolean-valued clothing, with the same blind spot.
2. Concretely, the internal unit interval of `V^{(Proj 𝒜)}` is the set of effects of `𝒜`
   (Takeuti: internal reals = self-adjoint operators affiliated with `𝒜`) but its internal
   order is the *spectral order* `≤_s` (Olson), not the effectus order. The pair of C1,
   `a = 0.6·p ≤ b = (1+q)/2` in `Pred M_2`, is **not** spectrally ordered: for
   `λ ∈ [½, 0.6)` one needs `E_a(λ) = p^⊥ ≥ E_b(λ) = q^⊥`, false. So `V^{(Q)}` internalises
   `(Pred X, ≤_s)`, a complete lattice that is not the effect algebra `Pred X`; theorems about
   `≤` cannot come out of it.

*Residue.* By Olson, for positive `a, b`: `a ≤_s b` iff `aⁿ ≤ bⁿ` for all `n`. In an
`&`-effectus `aⁿ = a & ⋯ & a`, so the spectral order is `&`-definable, and the honest
conjecture is "the Takeuti reals of `V^{(SPred X)}` are `(Pred X, ≤_&)` for an `&`-effectus";
that is a statement about `&`, not about toposes, and is not pursued here.

## C4. Every "spatial commutative" effectus is `Set`/`Kl(𝒟)`/measure-algebra-like

**Conjecture (as seeded).** An effectus all of whose objects are duplicable (a Markov
category) is a sub-effectus of `Kl(𝒟_M)`, `M` its scalars; in particular no commutative
effectus with quotients and comprehension escapes `Set`, `Kl(𝒟)`, `CvNᵒᵖ`.

**KILLED, cheaply.** `Kl(Radon) = cC*ᵒᵖ` (new-base Prop 1.1) is Markov, has quotients
`β(coz a)` and comprehension `{a = 1}`, scalars `[0,1]`, and is none of the three: it has
non-finitely-supported states (so no faithful state-preserving functor into `Kl(𝒟_M)`,
whose states are finite convex combinations of points), and it has no images (a non-isolated
point of the Cantor set has no least clopen neighbourhood), so it is not a ⋄-effectus and not
`CvNᵒᵖ`. Its ⋄-coreflection is exactly new-base Cor 1.4 (hyperstonean = clopen supports of
normal measures); C2's basically-disconnected criterion is the same "closure of support is
open" condition one level up, over a base.

**Lemma L (SURVIVED; proved). Duplicable objects of a monoidal ⋄-effectus have Boolean
sharp predicates.** Assume a ⋄-effectus with `⊗` such that for predicates `s` on `X`, `t` on
`Y` there is `s ⊗ t` on `X ⊗ Y`, monotone and additive in each argument, with
`(s ⊗ 1)(x ⊗ y) = s ∘ (id ⊗ !)`; and `δ : X → X ⊗ X` with `(id ⊗ !) ∘ δ = id = (! ⊗ id) ∘ δ`
(counitality only; no naturality, no commutativity). Then for sharp `s, t` on `X`:
`u := (s ⊗ t) ∘ δ` and `u' := (s ⊗ t^⊥) ∘ δ` satisfy `u ⊕ u' = (s ⊗ 1) ∘ δ = s`,
`u ≤ s`, `u ≤ t`, `u' ≤ s`, `u' ≤ t^⊥`. In a ⋄-effectus `v ≤ r` sharp gives `⌈v⌉ ≤ r`, so
`P := ⌈u⌉ ≤ s ∧ t` and `Q := ⌈u'⌉ ≤ s ∧ t^⊥`; these two meets are orthogonal, so `P ⊥ Q` and
`P ∨ Q = P ⊕ Q`. Hence `s = u ⊕ u' ≤ P ⊕ Q ≤ (s ∧ t) ∨ (s ∧ t^⊥) ≤ s`, i.e. `s` commutes
with `t` in the OML `SPred X` for all `s, t`; an OML in which all pairs commute is Boolean.
Checks: `vNᵒᵖ` (duplicable = `ℓ^∞(X)`, `SPred = 2^X`), `Kl(𝒟_M)`, `Kl(Radon)`-style
examples all agree; no counterexample found. Consequence for the hunt: a Markov ⋄-effectus
has *no* Bohrification problem — its sharp fibres are already Boolean — so C1's failure is
exactly the failure of duplicability, and a "quantum topos" over a ⋄-effectus, if one
exists, must be indexed by duplicable *sub*-objects (comprehensions of Boolean blocks), which
is `𝒞(𝒜)` again. Loop closed; nothing new is available from the topos side.

## Where a fresh attack would go (not run)

* Heunen–Jacobs dagger kernel categories: is `Pure(C)` with the dagger of eff.tex's
  `dagger-theorem` a dagger kernel category whose kernel subobjects are `SPred`? In `vNᵒᵖ`
  kernels should be comprehensions of `(im f)^⊥`; one would test `ker` against Paschke
  purity. A match would make Cho's OML a special case of Heunen–Jacobs's; a mismatch would be
  the first effectus-native quantum logic not of kernel type. Half a day, no topos content.
* C2's ⇒ direction for non-constant sheaves and the locality of basic disconnectedness.
