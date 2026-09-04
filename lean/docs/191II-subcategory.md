# 191II — "equivalent to a subcategory of `EMod_M^op`"

*(Answers `DECISIONS.md` §2.3; audit row
`bdils-pure-beff-states-effectalgebras.csv:90`, `left-ruling`.  Re-read here:
eff.tex 175I, 179II, 180I, 190II, 191I–191VIII;
`Theses/B/Eff/StatesPredicates.lean:1548–1590`.)*

## Verdict

**No counterexample exists, and none can.**  Every effectus `C` in total form
with scalars `M` and separating predicates is **isomorphic** — not merely
equivalent — to a (non-full) subcategory of `EMod_M^op`; §1 proves it by
retagging, with no new mathematics.  Consequently, for `D = EMod_M^op`,
"`C` is equivalent to a subcategory of `D`" and "there is a faithful functor
`C → D`" are **interderivable**.  §2.3's options (b) and (c) are therefore the
*same statement*, and 191II is true exactly as printed, on the standard
(non-full) reading of "subcategory".  What is defective is not the Theorem but
the closing sentence of **191VII**, which names *the* subcategory `Pred C` —
the literal image, an object that need not exist (§4).  Option (a), fullness,
is **false**: §5 gives a counterexample in `Set`.

## 1. The retagging theorem

**Lemma.**  Let `F : C → D` be faithful, and suppose there is a family
`(d_X)` of objects of `D`, indexed by `ob C`, with `d_X ≅ F X` and
`d_X = d_Y ⟹ X = Y`.  Then `C` is isomorphic to a subcategory of `D`.

*Proof.*  Fix isomorphisms `ι_X : F X → d_X`.  Put `G X := d_X` and, for
`f : X → Y`, `G f := ι_Y ∘ F f ∘ ι_X⁻¹ : d_X → d_Y`.  Conjugation by a family
of isomorphisms is functorial, so `G` is a functor; `G f = G g` gives
`F f = F g` gives `f = g`, so `G` is faithful; and `G` is injective on
objects.  Let `S` have objects `{d_X}` and arrows
`S(d_X, d_Y) := {G f : f ∈ C(X, Y)}` — well defined because `X ↦ d_X` is
injective, so each pair of objects of `S` is `(d_X, d_Y)` for exactly one
`(X, Y)`.  It has identities (`G 1_X = 1_{d_X}`) and is closed under
composition: if `G f : d_X → d_Y` and `G g : d_{Y'} → d_Z` are composable in
`D` then `d_Y = d_{Y'}`, so `Y = Y'`, so `g ∘ f` exists in `C` and
`G g ∘ G f = G(g ∘ f)`.  So `S` is a subcategory of `D`.

`G` corestricts to `G' : C → S`, bijective on objects (injective by
hypothesis, surjective by construction) and on each hom-set (surjective by
construction of `S`, injective by faithfulness) — hence an isomorphism of
categories. ∎

Injectivity on objects is the *only* thing faithfulness fails to give, and it
is a labelling matter — which is why the lemma is purely formal.  §2.3's
discrete-two-object example does not touch it: the terminal category has no
two distinct objects, so the hypothesis on `(d_X)` fails.

**Application.**  Let `C` be an effectus in total form with `Scal C = M` and
separating predicates; by 191VII, `Pred : C → EMod_M^op` is faithful.  For
each `X` let `P̃_X` be the `M`-effect module with carrier `|Pred X| × {X}`,
structure transported along `p ↦ (p, X)`: `0 := (0, X)`, `1 := (1, X)`,
`(p,X) ⊥ (q,X)` iff `p ⊥ q` and then `(p,X) ⊕ (q,X) := (p ⊕ q, X)`, and
`λ · (p,X) := (λ · p, X)`.  Every axiom of 175I and 179II is an equation or a
Horn clause in the operations, so it transports; `P̃_X` is an `M`-effect module and
`ι_X : Pred X → P̃_X` an isomorphism in `EMod_M`.  Effect-algebra carriers are
non-empty (they contain `0`), so `X ≠ Y` forces `|P̃_X| ∩ |P̃_Y| = ∅`, hence
`P̃_X ≠ P̃_Y`.  The Lemma applies, with action `G f (q, Y) = (q ∘ f, X)`.  ∎

## 2. (i) Does retagging stay inside `EMod_M`?

Yes.  179II defines `EMod_M` as *the* category of effect modules over `M`,
with no constraint on carriers; `|Pred X| × {X}` is a set (`Pred X` a hom-set,
`X` an object) carrying the transported structure, so `P̃_X ∈ EMod_M`.  Under
a Grothendieck-universe reading (carriers in `𝒰`, `C` a `𝒰`-category) the tag
stays inside too, `𝒰` being closed under pairing and products.  It is
canonical — no choice is used — and fails only if `ob C` is a proper class of
proper classes, where one tags along a class injection `ob C → V`.

## 3. (ii) What the printed sentences can mean

**191II, the Theorem.**  "…is equivalent to a subcategory of `EMod_M^op`" —
indefinite article, no `full`.  Under the standard definition (a subclass of
objects plus a subclass of arrows per pair, closed under identities and
composition) this is *existential*, and §1 proves it outright in the stronger
"isomorphic to" form: **the printed Theorem needs no repair**.  Its
neighbourhood confirms the reading: 191I motivates it as *universality* of
`EMod_M^op` among effectuses with scalars `M` ("in the following strong
sense"), and 191VIII is the negative companion (`Rng^op` fails *separating
predicates*, not fullness).  Fullness is nowhere in view — and is false (§5).

**191VII, the closing sentence.**  "So if `C` has separating predicates, `C`
is equivalent to the subcategory `Pred C` of `EMod_M^op`."  This names a
specific object, the literal image, and that is where the argument breaks, in
two ways.  First, the image of a functor need not be a subcategory at all:
`Pred f` and `Pred g` can be composable in `EMod_M^op` without `f, g` being
composable in `C`, whenever `Pred` identifies two objects.  Second, whether
`Pred` identifies objects is **not a property of `C`**: it depends on the
set-theoretic encoding of the arrows of `C`.  If an arrow is a triple
`(dom, cod, data)`, then `Pred X = Pred Y` forces `X = Y` (read the codomain
off `0 ∈ Pred X`), the image *is* a subcategory, and 191VII is right by
accident.  If an arrow is its bare underlying function — the usual convention
for a concrete category — the image can fail to be a subcategory; §4 exhibits
that in the thesis's own flagship effectus.  A sentence true under one
encoding of the same category and false under another cannot be the intended
content.  The retagging of §1 is the encoding-independent repair, one clause
long.

## 4. Where the literal image fails: `vN_cpu^op`

Work in `C = vN_cpu^op` (180V), arrows `X → Y` being ncpu maps `Y → X`, with
`1 = ℂ` and `1 + 1 = ℂ²`, so `Pred X = {ncpu maps ℂ² → X}`, which under
`p ↦ p(1,0)` is `[0,1]_X`, and `Pred f = φ|_{[0,1]}` for the ncpu `φ`
underlying `f`.  Take arrows to be bare functions.

The opposite algebra `A^op` (same set, same `*`, same linear structure,
reversed product) is a *different object* of `vN` with the *same* underlying
set, positive cone and unit — so `[0,1]_A = [0,1]_{A^op}` **literally**, and a
positive unital map `ℂ² → A` is the same function as one `ℂ² → A^op`
(positivity out of a commutative algebra is already complete positivity).
Hence `Pred A = Pred A^op` in `EMod_{[0,1]}`.  Let `D := M₂ ⊕ M₂` and
`D' := M₂ ⊕ M₂^op`, so `Pred D = Pred D'` too, and let `T` be the transpose, a
`*`-isomorphism `M₂ → M₂^op` and hence ncpu.  Take `ψ := ⟨id, T⟩ : M₂ → D'`
(ncpu), giving `f : D' → M₂` in `C`, and
`φ := (a,b) ↦ (a+b)/2 : D → M₂` (ncpu), giving `g : M₂ → D` in `C`.  Now
`f` and `g` are **not** composable in `C` (`cod g = D ≠ D' = dom f`), but
`Pred g : Pred M₂ → Pred D` and `Pred f : Pred D' → Pred M₂` **are**
composable in `EMod^op`, since `Pred D = Pred D'`.  Their composite is, on
effects, `a ↦ (a + aᵀ)/2 = ((id + T)/2)|`, whose Choi matrix
`(|Ω⟩⟨Ω| + SWAP)/2` is `-1/2` on the antisymmetric subspace: `(id+T)/2` is not
completely positive, and neither is `T ∘ (id+T)/2 = (id+T)/2`, so it is not
co-completely-positive either.  A unital positive map is determined by its
restriction to effects, and the only von Neumann algebras with the same set,
cone and unit as `M₂` are `M₂` and `M₂^op` (Kadison: the identity would be a
unital order, hence Jordan, isomorphism, and a factor's Jordan structure pins
the product up to `op`).  So the composite is not `Pred h` for any `h` of
`C`.

**The image class of `Pred` is not closed under composition; "the subcategory
`Pred C`" does not exist.**  To keep this finite, replace `vN` by the
sub-effectus of finite products of copies of `ℂ`, `M₂`, `M₂^op` — a full
subcategory of `vN^op` containing `1` and closed under coproducts, hence
itself an effectus in total form with real scalars and separating predicates,
in which the algebras with `Pred Z = Pred M₂` are visibly just `M₂, M₂^op`.
Here `M₂ ≅ M₂^op`, so that merge is between *isomorphic* objects.  It can
also merge non-isomorphic ones: for Connes' factor, `Pred A = Pred A^op` while
`A ≇ A^op` in `C` (an ncpu map with ncpu inverse is a unital order
isomorphism, hence Jordan, hence a `*`- or `*`-anti-isomorphism `A → A^op`;
the first is excluded by Connes, the second would make the non-2-positive
identity `A → A^op` completely positive).  Whether the subcategory *generated
by* the image is nonetheless equivalent to `C` is a separate, hard and —
given §1 — irrelevant question, not settled here.

## 5. (iii) Fullness is false

`Pred : Set → EA^op = EMod_2^op` (`Set` is an effectus with scalars `2` and
separating predicates, 190III.3a) is **not** full.  `Pred ℕ = P(ℕ)`,
`Pred 1 = 2`, and an `EA`-homomorphism `h : P(ℕ) → 2` is exactly a finitely
additive `{0,1}`-measure with `h(ℕ) = 1`, i.e. an ultrafilter on `ℕ`; those in
the image of `Pred` are the preimage maps `U ↦ [n ∈ U]`, the *principal*
ultrafilters.  Non-principal ones exist, and `Pred X ≅ 2` only for `|X| = 1`,
so fullness fails, as does fullness onto the essential image: option (a) of
§2.3 is not merely unproved but untrue.

## 6. What this means for the Lean statement

`emod_effectus_representation` (`StatesPredicates.lean:1574`) gives
`∃ F : Tot C ⥤ (EModCat.{v,v} (Scal C))ᵒᵖ` with object part pinned to
`(F.obj X).unop.carrier = Pred X.base`, morphism action pinned by `HEq`, and
`F.Faithful`.

1. **Keep it as it stands.**  Given §1, the pinned faithful functor *is* the
   whole content of 191II's second sentence: for this codomain, "equivalent to
   a subcategory" and "admits a faithful functor" are interderivable.  The
   statement is the Theorem minus a relabelling, not something weaker; the
   audit row's `weaker` verdict should become `ok`.
2. **Correct the ⚠ docstring.**  It says "What the image subcategory needs in
   addition is that `Pred` be full onto its image" — wrong twice over:
   full-onto-image does not rescue the inference (§2.3), and fullness is
   *false* (§5).  What is needed is injectivity on objects, which §1 gives for
   free.  The docstring should say so and point here; `left-ruling` can close.
3. **If the clause is wanted in Lean**, the idiomatic form is
   `∃ G : Tot C ⥤ (EModCat M)ᵒᵖ, G.Faithful ∧ Function.Injective G.obj`:
   mathlib has `ObjectProperty.FullSubcategory` and `WideSubcategory` but no
   general non-full `Subcategory`, and a faithful injective-on-objects functor
   *is* how a subcategory is presented.  Two warnings.  (α) The **naive tag
   fails**: `EModCat` bundles only `carrier : Type v` plus instances, so
   `G.obj X = G.obj Y` yields `carrier X = carrier Y` as a *type* equality,
   from which Lean gives only `Equiv.cast`, i.e. equinumerosity — `X` is not
   readable off `Pred X × {X}`.  The tag must be a **cardinal separator**:
   well-order `C`, put `o X := Ordinal.typein _ X`, let `μ` bound
   all `#(Pred X)`, and take the carrier
   `Pred X ⊕ (Cardinal.aleph (Ordinal.ord μ + o X)).out`; left cancellation of
   ordinal addition and strict monotonicity of `aleph` make `X ↦ #(G.obj X)`
   injective, and infinite-cardinal absorption makes it readable off the
   carrier.  (β) That costs a **universe bump**
   (`EModCat.{v, max u v}`) and weakens the object clause from
   `carrier = Pred X` to `(G.obj X).unop ≅ EModCat.of _ (Pred X)` — strictly
   worse than the present statement for every downstream use.

**Recommendation: (1) + (2).**  If the clause is wanted on the record
anyway, add it as a *separate* corollary
`emod_effectus_representation_subcategory`, leaving the pinned form the usable
one.
