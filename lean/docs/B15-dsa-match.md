# B15 addendum: do proc's and eff's "⋄-self-adjoint" coincide a posteriori in `vNᵒᵖ`?

**Question.** proc.tex **103I** calls `f : 𝒜 → 𝒜` ⋄-self-adjoint when it is
*pure* **and** contraposed to itself (`f^⋄ = f_⋄`). eff.tex **206II** calls
`f : X → X` in a ⋄-effectus ⋄-self-adjoint when `f^⋄ = f_⋄` (`diaPull f =
diaPush f`), with *no* purity. The tree already proves eff ⟹ contraposed. Do
the two notions coincide in `vNᵒᵖ`, i.e. does `diaPull f = diaPush f` force
`f` pure?

## Verdict: they do NOT match. eff-⋄-self-adjoint is strictly weaker.

`diaPull f = diaPush f` is **exactly** "contraposed to itself", not strictly
stronger, and does **not** force purity. Both directions between the two are
in the tree, at `Theses/B/Eff/VNExamples.lean`:

* eff ⟹ contraposed: `su_contraposed_of_diamondSelfAdjoint` (5408).
* contraposed ⟹ eff: `su_diamondSelfAdjoint_of_symm` (4521) turns symmetry of
  `f^⋄` into `diaPull f = diaPush f`, via 207III `diamond_adjunction`.

So in `vNᵒᵖ`: **eff-⋄-self-adjoint ⟺ contraposed-to-itself**, exactly. proc's
notion adds the independent purity clause on top, so proc ⟹ eff but **eff ⇏
proc**: the failing direction is precisely the purity clause. (`su_diaPull_val`
(4513) pins the concrete content: `f^⋄(z) = ⌈f(z)⌉`, so `f^⋄ = f_⋄` unfolds to
`⌈f(s)⌉ ≤ t^⊥ ⟺ ⌈f(t)⌉ ≤ s^⊥` for all projections — proc's 101VI
contraposition verbatim, with nothing about the Kraus rank of `f`.)

## The sum example settles it

Let `B₁, B₂ ∈ 𝒜` be self-adjoint, **linearly independent**, with `B₁²+B₂² ≤ 1`
(the sub-unitality bound). Put

    g = ad_{B₁} + ad_{B₂} :  x ↦ B₁ x B₁ + B₂ x B₂     (a normal cpsu endomap;  g(1) = B₁²+B₂² ≤ 1).

**`g` is eff-⋄-self-adjoint (`diaPull g = diaPush g`).** By `diamond-sum`
(proc parsec 1090 / eff), `(–)^⋄` and `(–)_⋄` of a sum are the join of the
summands':

    g^⋄(s) = ⌈g(s)⌉ = ⌈B₁sB₁ + B₂sB₂⌉ = ⌈B₁sB₁⌉ ∨ ⌈B₂sB₂⌉.

Test the symmetry that (via `diamond_adjunction` = `su_diamondSelfAdjoint_of_symm`)
is equivalent to `diaPull g = diaPush g`. For a projection `s` and each `i`:

    ⌈BᵢsBᵢ⌉ ≤ t^⊥  ⟺  t Bᵢ s Bᵢ t = 0  ⟺  s Bᵢ t = 0  (as ‖s Bᵢ t‖² = ‖t Bᵢ s Bᵢ t‖)
                    ⟺  t Bᵢ s = 0        (adjoint; Bᵢ = Bᵢ*)  ⟺  ⌈Bᵢ t Bᵢ⌉ ≤ s^⊥.

Taking the conjunction over `i = 1,2`:

    g^⋄(s) ≤ t^⊥  ⟺  (∀i) ⌈BᵢsBᵢ⌉ ≤ t^⊥  ⟺  (∀i) ⌈BᵢtBᵢ⌉ ≤ s^⊥  ⟺  g^⋄(t) ≤ s^⊥.

So `g^⋄` is symmetric — `g` is contraposed to itself, hence `diaPull g =
diaPush g`. (Equivalently: each `ad_{Bᵢ}` is contraposed to itself for `Bᵢ`
self-adjoint, so `g_⋄ = (ad_{B₁})_⋄ ∨ (ad_{B₂})_⋄ = (ad_{B₁})^⋄ ∨ (ad_{B₂})^⋄
= g^⋄`.)

**`g` is impure.** `{B₁, B₂}` is a minimal Kraus decomposition of `g`: since
`B₁, B₂` are linearly independent, `g` has Choi/Kraus rank 2. Pure maps in
`vNᵒᵖ` are exactly the single-Kraus conjugations `ad_V : x ↦ V*xV` (Choi rank
≤ 1). Rank 2 ⟹ `g` is not pure. (Concrete: `𝒜 = M₂`, `B₁ = diag(1,0)`,
`B₂ = diag(0,1)` — then `g = ` diagonal-restriction, `g(1)=1`, plainly not a
single conjugation.)

Hence **`g` is eff-⋄-self-adjoint but not proc-⋄-self-adjoint.** The two
definitions genuinely disagree; proc's is strictly stronger, by purity.

(No conflict with `docs/B15-pure-sqrt.md`: that theorem says a ⋄-self-adjoint
`g` whose *square* `g∘g` is *pure* is itself pure. This `g` has `g∘g` impure,
so it lies outside that hypothesis — consistent.)

## What it means for B15

Reading **(1)** — closing the `sorry` by adding `IsPure` to
`DiamondSelfAdjoint` — genuinely **changes the notion of ⋄-self-adjoint**, not
merely "picks the intended member": impure witnesses like `g` above are
eff-⋄-self-adjoint and would be excluded. So the two ⋄-self-adjoint notions
are different objects, and the author should know that. Crucially, this does
**not** carry over to ⋄-*positivity*: there the square `g∘g` is pure, and
`B15-pure-sqrt.md` shows the root `g` is then automatically pure — so the
⋄-positive class is the same under either reading, and the `sorry` remains a
legitimate either-way choice for that application alone.
