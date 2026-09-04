# B15 reading (3): an elementary proof, without Kadison

**Target.** In `vNᵒᵖ`: `g : 𝒜 → 𝒜` ncp, *self-contraposed* (`g^⋄ = g_⋄`, the
eff-206II notion, **no purity assumed**), and `f := g∘g` pure.  Show `f` is
A-⋄-positive, i.e. `f = √q(·)√q` with `q := f(1)`.

## Verdict: elementary proof found, with one named gap

Complete and Kadison-free **whenever `p := g(1)` is invertible in its own
corner** — in particular for every finite-dimensional `𝒜`.  In general it
rests on one sub-claim, **(S)** below (`g` is *onto* its corner).  Three
by-products worth the author's attention:

* the Kadison proof in `B15-pure-sqrt.md` has the **same** gap — its Step 2
  reads "a pure map is an order-isomorphism *onto* its corner", false for a
  filter `√q(·)√q` with `q` non-invertible.  Kadison buys nothing here, and
  cannot: it needs a bijection, which is what is missing.
* no Kadison–Schwarz for ncp maps is needed: once the maps are normalised to
  be unital, **99IX** (`iso`, via Gardner **99II**) does the work — in Lean.
* the Kraus route, which `B15-pure-sqrt.md` calls "genuinely awkward", closes
  in six lines for *arbitrary* Kraus rank once the Kraus span is `*`-closed
  (§7), with no invertibility needed.

Conventions: `ad_a = a*(·)a`; `⌈·⌉` carriers; `c_p = √p(·)√p` the standard
filter, `π_s` the standard corner; `f^⋄(s) = ⌈f(s)⌉`, `f_⋄` its contraposition
(**101I/101II**); `[f]` the ncpu part of `square-f`.

## 1. Contraposition alone pins the carrier

`⌈h⌉ = h_⋄(1)` and `⌈h(1)⌉ = h^⋄(1)` for any ncp `h`, so **`g^⋄ = g_⋄` gives
`e := ⌈g⌉ = ⌈g(1)⌉` outright** — proc **103III**.1 without its purity
hypothesis.  Hence `g(x) = g(exe)` (carrier) and `g(x) ≤ ‖x‖p ∈ e𝒜e`, so `g`
restricts to a normal cp endomap of `M := e𝒜e`, with `g(1_M) = p`,
`⌈p⌉ = 1_M`.  Likewise `f^⋄ = g^⋄g^⋄ = g_⋄g_⋄ = f_⋄`, and
`⌈f⌉ = g_⋄(g_⋄(1)) = g^⋄(e) = ⌈g(e)⌉ = ⌈g(1)⌉ = e = ⌈f(1)⌉`.

*Degenerate cases.*  `f = 0` forces `e = ⌈f⌉ = 0`, i.e. `g = 0`, and the
conclusion is trivial.  `p` non-faithful in `𝒜` is not a case at all: the
whole argument runs inside `M`, and the descent from `M` back to `𝒜` is
proc **105V**, *already formalised* (`positive_map_uniqueness`, which calls
**104IX** on the corner exactly this way).

## 2. The shape of `f`

`f` is pure and `⌈f⌉ = 1_M` on `M`, so `f` is a filter (**100VII**.1), and by
uniqueness of filters (**98II**) `f = c_q ∘ ϑ`, `ϑ` an ncpu-automorphism of
`M`, which is nmiu by **99IX**.  So on `M`

    f(x) = √q ϑ(x) √q ,   q = f(1),  ⌈q⌉ = 1_M .           (1)

The target is precisely `ϑ = id`.

## 3. Inverting `g` — the one place a hypothesis is needed

**(S)  `g(M) = M`.**  Granted (S): `f = g∘g` is then surjective too, and `f`
is injective by (1) (`√q x √q = 0 ⟹ x = 0` as `⌈q⌉ = 1`), so `g` is a linear
bijection of `M` with

    g⁻¹ = g ∘ f⁻¹ ,   f⁻¹ = ϑ⁻¹ ∘ c_{q⁻¹} ,

both **normal cp** — `q` is invertible because `√q M √q = f(M) = M`.  Set
`K := ‖g⁻¹‖ < ∞`.  For `0 ≤ y ≤ 1` we get `y = g(g⁻¹y)` with
`0 ≤ g⁻¹y ≤ K·1`, so `y ≤ K·g(1) = Kp`; at `y = 1`, `1 ≤ Kp`:

    p is invertible in M.                                    (2)

(Conversely `q = √p γ(p) √p` with `γ := [g]`, so `p` invertible ⟺ `q`
invertible ⟺ (S).  This is the *only* use of (S).)

## 4. Normalise, then 99IX — no Schwarz, no Kadison

With (2), put

    φ := c_{p⁻¹} ∘ g|_M  :  x ↦ p^{-1/2} g(x) p^{-1/2} .

`φ` is normal cp and **unital**; it is bijective with
`φ⁻¹ = g|_M⁻¹ ∘ c_p`, normal cp, and unital (`φ⁻¹(1) = g⁻¹(p) = 1`).  So `φ`
and `φ⁻¹` are both ncpu, and **99IX** (`iso`: an ncpsu-isomorphism is an
nmiu-isomorphism, proved from Gardner **99II**) makes `φ` an
nmiu-automorphism of `M`.  Hence

    g|_M = c_p ∘ φ  =  filter ∘ isomorphism,

so `g = c_e ∘ c_p ∘ φ ∘ π_e` is **pure** (**100I**).  Being pure and
contraposed to itself, `g` is ⋄-self-adjoint in proc's sense (**103I**), so
`f = g∘g` is ⋄-positive, and **105V** gives `f = √q(·)√q`.  ∎ (mod (S))


*On the brief's step (2).*  The Choi/Kadison–Schwarz route is this same
argument: KS for `φ` and `φ⁻¹` gives
`x*x ≤ φ⁻¹(φ(x)*φ(x)) ≤ φ⁻¹(φ(x*x)) = x*x`, so `φ(x*x) = φ(x)*φ(x)` by
injectivity of `φ⁻¹` (faithfulness is not needed), and the multiplicative
domain is everything.  It buys nothing over 99IX and costs a Schwarz
inequality for maps that the tree does not have.  Both forms need the maps
**unital on both sides**: the ‖h‖-normalised Schwarz
`h(x)*h(x) ≤ ‖h(1)‖ h(x*x)` degrades the sandwich to `x*x ≤ K²x*x` and the
equality is lost.  Unitality is bought only by dividing by `√p` — i.e. by
(2), i.e. by (S).  So the answer to "is normalisation needed?" is: yes, and
it is *exactly* the gap.

## 5. The gap, precisely

**(S) `g` is surjective on `M := ⌈g⌉𝒜⌈g⌉`; equivalently `g(1)` is invertible
there; equivalently `f(1)` is.**  This is not vacuous and not free: `g = c_p`
with `p` faithful but not invertible satisfies every hypothesis (and is pure,
so the theorem holds for it — the *proof* is what stalls).  Everything before
and after §3 is hypothesis-free.

`B15-pure-sqrt.md` Steps 2–3 assume (S) silently, confusing the carrier of a
pure map with its range: with `q` non-invertible `f(M) = √q M √q ⊊ M`, `f`
has no bounded inverse, and Kadison's theorem — about bijections — does not
apply.  Both routes are gapped in the same spot; the elementary one
dominates.

## 6. Any proof must use purity of `f` on the nose

It is tempting to work only with `G := g^⋄`, prove `G² = P²` for
`P := c_p^⋄`, and finish with **104VII** at `(p, √q)` — 104IX's own endgame.
But `G² = P²` does not follow from self-contraposition: for `g =` diagonal
restriction on `M₂` (`= ad_{E₁₁} + ad_{E₂₂}`, self-contraposed, `p = 1`, so
`P = id`), `G²(s) = 1 ≠ s` at `s` the projection on `(1,1)/√2`.

## 7. Unconditional partial results

**(a) Finite dimensions.**  By §1 take `⌈f⌉ = ⌈f(1)⌉ = 1`; `f` pure means
`f = ad_W`, and `⌈WW*⌉ = ⌈W*W⌉ = 1` makes `W` invertible.  With
`g = Σᵢ ad_{Aᵢ}`, `f`'s Kraus family is `{AᵢAⱼ}`, so `AᵢAⱼ = cᵢⱼW`; some
`cᵢⱼ ≠ 0` (else `f = 0`, so `g = 0`), whence `Aᵢ, Aⱼ` are invertible and
`A_k = c_{ik}Aᵢ⁻¹W` for every `k`: Kraus span one-dimensional, `g` pure.

**(b) The Kraus route, all ranks, no invertibility.**  *Lemma.  Let `V` be a
`*`-closed subspace of a C\*-algebra with `V·V ⊆ ℂW`.  Then `dim V ≤ 1`.*
Proof.  `V` is spanned by its self-adjoints.  Take `B = B* ∈ V`, `B ≠ 0`;
`B² ∈ ℂW` is nonzero, so `W = B²` w.l.o.g.  Let `C = C* ∈ V`, write
`BC = αB²`, so `CB = ᾱB²`, and put `D := C − (Re α)B = D* ∈ V`.  Then
`BD = ibB²` and `DB = −ibB²` with `b = Im α`, and `D² = c B²` with `c` real
and `≥ 0`.  Now `cB³ = D²B = D(DB) = (DB)B = −b²B³`, and `B³ ≠ 0`, so
`c = −b²`; with `c ≥ 0`, `b² ≥ 0` this forces `c = b = 0`, hence `D² = 0`,
`D = 0`, `C = (Re α)B`. ∎

If `g = Σᵢ ad_{Aᵢ}` has `*`-closed Kraus span `V` (e.g. all `Aᵢ` self-adjoint
— the family of `B15-dsa-match.md`, automatically self-contraposed), then
`f = g∘g` pure means `V·V ⊆ ℂW`, so `dim V = 1` and `g = ad_B` is pure: the
"impure ⋄-self-adjoint root" dies at every rank at once, generalising the
`M₂` hand computation in `DECISIONS.md`.  `*`-closedness is sufficient for
self-contraposition, not known to be necessary (which only says
`sVt = 0 ⟺ sV*t = 0` for projections `s,t`), so (b) is not the theorem.

**Recommended attack on (S).**  Lemma (b) is about the space of Kraus
operators; its type-free avatar is the intertwiner module of the minimal
Stinespring/Paschke dilation (dils.tex), where `V·V ⊆ ℂW` says "the dilation
of `g∘g` has multiplicity one" and `⌈g⌉ = ⌈g(1)⌉` rules out `V·V = 0`.
Running the lemma's computation in that module is the only route in sight
that does not need `g` invertible.

## 8. Lean

Grep of `Theses/` for `schwarz`/`Schwarz`/`kadison`: **there is no
Kadison–Schwarz inequality for maps.**  The only Kadison-named declaration is
`npf_kadison` (`Theses/A/CStar/TowardsVN.lean:2233`), Kadison's inequality
`|ω(a*b)|² ≤ ω(a*a)ω(b*b)` for a *normal positive functional* (**30IV**.1);
the rest of the hits are Cauchy–Schwarz for `𝒜`-valued inner products
(**32VI**, `A/CStar/Matrices.lean`) or prose.  Choi and Russo–Dye for cp-maps
are in the same file (**34XVI**, **34XVIII**).  None of them is needed.

What is needed is all present, in `A/Proc/Measurement.lean`: **99IX** `iso`
(:3425), **100III** `pure_fundamental` (:4430), **103I**
`IsDiamondSelfAdjoint`/`IsDiamondPositive` (:5770), **104VII**
`positive_quotients_centrally_similar`, **104IX**
`faithful_positive_map_uniqueness` (:8400) and **105V**
`positive_map_uniqueness` (non-faithful descent to the corner included).

**Cost, if (S) is granted or the invertible case suffices:** new content is
§1 (carrier from contraposition — `purely_positive_basic_1` with the purity
hypothesis dropped), §3 (bounded inverse ⇒ `1 ≤ Kp`), §4 (normalise, cite
`iso`), then `positive_map_uniqueness`.  Mathematically tiny; in Lean the
cost is the `Corner A e` transport that `positive_map_uniqueness` already
pays twice over — estimate **500–800 lines**, no new imports, no mathlib
gaps.  `su_exists_asrt` (`B/Eff/VNExamples.lean`) needs (S) too, so reading
**(1)** (add `IsPure` to `DiamondSelfAdjoint`) stays the cheap route today.
