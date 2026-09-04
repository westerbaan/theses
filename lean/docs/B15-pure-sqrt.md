# B15 reading (2): the pure ⋄-self-adjoint square root

**Question.** In `vNᵒᵖ` (normal cpsu maps between von Neumann algebras,
Heisenberg picture; pure = single Kraus `ad_V : x ↦ V*xV`; ⋄-self-adjoint =
contraposed to itself, `f^⋄ = f_⋄`): if `g` is ⋄-self-adjoint and `g∘g` is
pure, is there a **pure ⋄-self-adjoint** `h` with `h∘h = g∘g`?

## Verdict

**YES — provable in all types (I / II / III).** In fact `g` is *itself* pure,
so one may take **`h = g`**. The extra step reading (2) needs is therefore
*true*, not open. (Consequence: the "impure square root breaks uniqueness"
worry cannot occur — see the last section.)

Conventions below: `ad_V(x)=V*xV`; a CP `g` has Kraus form `g(x)=Σ_i A_i* x A_i`;
`⌈·⌉` is the carrier (support projection); `e := ⌈g⌉`.

## The reduction (confirmed, and then bypassed)

*Confirmed.* A pure ⋄-self-adjoint `h` is `ad_V` (single Kraus). `ad_V∘ad_V(x)
= V*(V*xV)V = (V²)* x V² = ad_{V²}(x)` (no self-adjointness needed for this
identity). ⋄-self-adjointness of `ad_V` forces `V = λB`, `|λ|=1`, `B=B*`
(from `f^⋄=f_⋄`: for a rank-one `s=|ξ⟩⟨ξ|`, `⌈V*sV⌉=span{V*ξ}` must equal
`⌈VsV*⌉=span{Vξ}`, so `V*ξ ∥ Vξ` for all `ξ`, i.e. `V*=cV`, `|c|=1`; put
`B=√c·V`). Hence `V²=λ²B²` and `ad_{V²}=ad_{B²}` with `B²≥0`. So **a pure
⋄-self-adjoint square is exactly `ad_c` with `c≥0`**, and conversely
`h=ad_{√c}` works. Existence of `h` ⟺ `g∘g = ad_c` for some `c ≥ 0`.

*Bypassed.* We do not have to test this on `g∘g` directly: we show `g` itself
is pure, and then `h=g` already satisfies the three requirements (pure,
⋄-self-adjoint by hypothesis, and `h∘h=g∘g`). In type I this reproves the
reduction with `c = S² ≥ 0` for the self-adjoint `S` with `g = ad_S`.

## Proof that `g` is pure

The Kraus route (all products `A_iA_j ∝ W`) is genuinely awkward and, as the
prompt notes, dies in type II/III. The structural route via the minimal
Stinespring dilation is clean and type-independent.

**Step 1 — `g` preserves one corner.** `g∘g` is ⋄-self-adjoint (proc 1030.30.2)
and `⌈g∘g⌉=⌈g⌉=e` (proc 1030.30.1/.2). For a ⋄-self-adjoint map proc 1030.30.1
gives `⌈g⌉=⌈g(1)⌉`: the domain carrier and the image support coincide, both
`= e`. So `g` restricts to a normal CP endomap of the corner `e𝒜e`, and
likewise `g∘g : e𝒜e → e𝒜e`.

**Step 2 — a pure map is an order-isomorphism onto its corner.** `g∘g` is
pure, so by the multiplicity-one (minimal Stinespring) characterization it is
of the form `x ↦ V*α(x)V` with `α` a normal `*`-homomorphism — a corner ∘
`*`-isomorphism ∘ compression. Such a map is a **normal CP order-isomorphism
of `e𝒜e` onto its image corner**, and by Step 1 that image corner is again
`e𝒜e`. Hence `g∘g` is an *order-automorphism* of `e𝒜e`: linearly bijective,
order-preserving both ways, with `(g∘g)^{-1}` again normal CP. (Type I sanity
check: `g∘g = ad_W`, and on `e𝒜e = B(eH)` with `W` invertible on `eH`, `ad_W`
is bijective with inverse `ad_{W^{-1}}`.)

**Step 3 — `g` is an order-automorphism with CP inverse.** `g∘g` bijective on
`e𝒜e` forces `g` injective and surjective there, so `g` is a linear
bijection. Its inverse is `g^{-1} = g ∘ (g∘g)^{-1}`, a composite of two normal
CP maps, hence **normal CP**. So `g` is a normal CP order-automorphism of
`e𝒜e` whose inverse is also CP.

**Step 4 — Kadison / the CP-sandwich theorem.** A normal bijection that is
2-positive with 2-positive inverse is a `*`-isomorphism twisted by a
conjugation: `g(x) = C α(x) C*` for an invertible `C ∈ e𝒜e` and a normal
`*`-**automorphism** `α` of `e𝒜e`. (This is Kadison's order-isomorphism
theorem together with the Jordan decomposition of the resulting Jordan
automorphism into a `*`-automorphism and a `*`-anti-automorphism; complete
positivity — already 2-positivity of `g` *and* of `g^{-1}` — kills the
anti-automorphism branch, since the transpose is positive but not 2-positive.
Refs: Kadison 1951; Choi 1975 for `B(H)`; Størmer for the general vN case.)

**Step 5 — that is a pure map.** `g(x) = C α(x) C*` is a compression `ad_{C*}`
after a `*`-isomorphism `α`: this is precisely a pure map in the sense of
100I (`IsPure`), which includes `*`-isomorphisms. Hence **`g` is pure**, and
`h := g` is a pure ⋄-self-adjoint map with `h∘h = g∘g`. ∎

**Type-I refinement.** In `B(H)` every automorphism `α` is inner
(`α = ad_{U*}`, `U` unitary), so `g = ad_{(CU)*}` is a genuine single-Kraus
`ad_V`. Feeding `g` pure back through the "reduction" section: `g` pure +
⋄-self-adjoint ⟹ `V = λS`, `S=S*`, so `g = ad_S` and `g∘g = ad_{S²}` with
`S² ≥ 0`. This is `ad_c`, `c = S² ≥ 0`, exactly the reduction, now *derived*
rather than assumed. The M₂-by-hand result in `QUESTIONS.md`/`DECISIONS.md`
is the `n=2` instance.

**On the single-Kraus phrasing.** "Pure = single Kraus `ad_V`" is the type-I
shadow of purity. In type II/III with an *outer* `α` the map `g = Cα(·)C*` is
pure (100I) but not literally `ad_V`; that is why the Kraus computation stalls
there while the Stinespring/order-iso argument does not. The Lean `IsPure`
tracks the 100I notion, so `h = g` is `IsPure` in every type.

## Bearing on the Lean tree and on the (1)/(2) reading

The open `sorry` in `vn_is_andthen_eff` (via `su_exists_asrt`,
`Theses/B/Eff/VNExamples.lean`) is exactly

    ∀ {X} (g : X ⟶ X), DiamondSelfAdjoint g → IsPure (g ≫ g) →
      ∃ h, IsPure h ∧ DiamondSelfAdjoint h ∧ g ≫ g = h ≫ h

and the argument above shows the witness can be `h := g`: the content is
"`DiamondSelfAdjoint g ∧ IsPure (g≫g) → IsPure g`". So the statement is **true**,
and reading (2) is mathematically **sound** — 211IV's citation of 105V leaves a
real gap, but a *fillable* one, and the "impure ⋄-self-adjoint root" that would
break the uniqueness in 211II.1 provably does not exist (any ⋄-self-adjoint `g`
with `g∘g = ad_b`, `b` indefinite self-adjoint, would by Step 5 be `ad_S` with
`g∘g = ad_{S²}`, `S²≥0 ≠ ±b`: contradiction). Uniqueness is safe either way.

For discharging the tree, though, a Lean proof of the step needs Kadison's
order-isomorphism theorem (equivalently the CP-sandwich theorem) for von
Neumann algebras, which is not in mathlib and is a substantial formalization.
The evidence therefore favours, for the author, that **(2) is defensible as
printed** (no wording change forced, the missing lemma is a true theorem); but
for closing the `sorry` cheaply, **(1)** — adding an `IsPure` conjunct to
`DiamondSelfAdjoint`, which is proc.tex 103I's own definition and under which
the redundant hypothesis makes `h=g` immediate — remains the pragmatic route.
The two now agree on the mathematics; they differ only in how much machinery
the formal proof must carry.
