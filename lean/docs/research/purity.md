# Purity across effectuses: no randomness, no merging

Research note, 2026-09-12, building on `docs/B15-S.md`, `docs/B15-dsa-match.md`
and today's commutative/Kleisli observations. Mathematics only, no Lean;
"Thm" = proved in the note, "Conj" = evidence only. Thesis references: proc
**100III** `pure-fundamental`, **99II** `gardner`, **102II** `rigid`,
**102III** `rigid-ncp-extreme`, **102V** `nmiu-rigid`, **102IX**
`pure-is-rigid`; eff **201II** (pure = `π∘ξ`), **206II** (⋄-notions),
**207III** `diamond_adjunction`, **211II** (`&`-effectus), **212III**
`standard-form-map`.

## 0. Setting and the zoo

Effectus arrow `f : X → Y`; in `vNᵒᵖ` this is ncp `f : 𝒜_Y → 𝒜_X`, `1∘f = f(1)`,
`im f = ⌈f⌉` (proc's carrier), `⌈1∘f⌉ = ⌈f(1)⌉`, `f^⋄(s) = ⌈f(s)⌉`, and
`f_⋄(s) = least t with s·f(t^⊥)·s = 0`. In an `&`-effectus every map has the
standard form (212III)

    f = π_{im f} ∘ h_f ∘ ζ_{⌈1∘f⌉} ∘ asrt_{1∘f},   h_f total and faithful, unique,

and `f` is pure iff `h_f` is an iso. Call `h_f` the **normalisation** of `f`.

| effectus | maps `X → X` | pure endomaps | `asrt_p` | pure ⋄-self-adjoint |
|---|---|---|---|---|
| `Set` (partial fns) | partial functions | partial injections | partial identity on `p` | partial involutions (involution of a subset `D`) |
| `Kl(𝒟)` | `x ↦ Σ_y g(x,y)δ_y`, mass ≤ 1 | `x ↦ w(x)·δ_{φ(x)}`, `φ` injective on `D = {w>0}` | `x ↦ p(x)δ_x` | `w·δ_ϑ`, `ϑ` an involution of `D` (any `w`) |
| `CvNᵒᵖ` | Markov kernels | `a ↦ b·(a∘φ)`, `φ` a measure-class injection | mult. by `p` | `b·(−∘ϑ)`, `ϑ` involutive, `b` arbitrary |
| `vNᵒᵖ` | ncp | `c_q ∘ ϑ ∘ π_e` (100III); in `B(H)`: `ad_V` | `ad_{√p}` | `ad_{√p} ∘ ϑ`, `ϑ` nmiu involution fixing `p` (B15-S repair) |
| `EJAᵒᵖ` | positive (sub)unital | `U_{√q} ∘ ϑ ∘ corner`, `ϑ` Jordan iso | `U_{√p}` | Conj: `U_{√p} ∘ ϑ`, `ϑ` involutive Jordan auto with `ϑ(p) = p` |

The `Kl(𝒟)` rows are proved below (§3); `Set` is the `M = {0,1}` case. The
`EJAᵒᵖ` row is by analogy with `vN` (quotients are quadratic maps `U_{√q}`,
comprehensions corners, eff 2100 ff.) and is *not* checked.

## 1. Purity = no randomness + no merging (Conj A, Thm in three examples)

**Conj A.** In an `&`-effectus with atomic-enough sharp predicates (below), a
map `f` is pure iff its normalisation `h := h_f` satisfies

  (R) **no randomness**: `s ∘ h` is sharp for every sharp `s` (`h` is a
      *sharp map*), and
  (M) **no merging**: `h_⋄ : SPred → SPred` is injective.

Both conditions are effectus-expressible, and must be put on `h`, not on `f`:

* `f = ad_V` in `B(H)ᵒᵖ` (non-multiplicative, e.g. `V` a non-normal
  contraction) is pure; `s∘f = V*sV` is not sharp, but
  `h_f = ad_{[V]}` (polar phase, a partial-isometry conjugation between
  corners) is nmiu, so (R) holds for `h_f`. Purity is a property of the
  normalisation, and 100III says exactly this.
* (M) fails on `f` itself even for pure faithful `f`: on `ℓ² = H`,
  `q = diag(1/n)`, `f = c_q`, `f_⋄(s) = [√q(ran s)]⁻` is `1` both for `s = 1`
  and for `s = ` projection onto `{v}^⊥` with `v = (1/n) ∉ ran √q` (then
  `(√q ran s)^⊥ = √q⁻¹(ℂv) = 0`). So "`f_⋄` injective" is *not* a purity
  invariant in type I∞; only `(h_f)_⋄` is. This is also why the abstract
  route in §2 stalls in infinite dimensions.

**Thm A (`vNᵒᵖ`).** For total faithful `h` (ncpu, `⌈h⌉ = 1`) between corners:
`h` iso ⟺ (R) ∧ (M). ⟸: (R) says `h(Proj) ⊆ Proj`, so `h` is nmiu by Gardner
(99II); nmiu + faithful ⟹ injective. For nmiu `h`, `h(t^⊥) = h(t)^⊥`, so
`h_⋄(s) = h⁻¹(least element of h(Proj) above s)` (`h(Proj)` is meet-closed by
normality). If some projection `s ∉ h(Proj)`, put `s' := least h(t) ≥ s`; then
`s' ≠ s` and `h_⋄(s') = h_⋄(s)`, contradicting (M). Hence `h(Proj) = Proj`
and `h` is onto (projections generate). ⟹ trivial.

**Thm A (`Kl(𝒟)`, `Set`).** `h : D → 𝒟(D)` total faithful. (R): `h(x)(S) ∈
{0,1}` for all `S` ⟹ `h(x) = δ_{φ(x)}`. (M): `h_⋄(S) = φ(S)` injective ⟹ `φ`
injective; faithful (`im h = D`) ⟹ `φ` onto. So `h` is a bijection. ∎

*Atomic-enough:* the `vN` proof used Gardner and lattice generation; the
`Kl(𝒟)` proof used points. A proof from the effectus axioms alone would need
"(R) ⟹ `h` preserves `∧` of sharp predicates" — the Gardner step — which I
see no way to get abstractly; hence Conj, not Thm.

## 2. The B15 theorem beyond `vN` (Thm B in `Set`, `Kl(𝒟)`; Conj B)

**Statement B.** `g : X → X` with `im g = ⌈1∘g⌉` and `g∘g` pure ⟹ `g` pure.

**Necessity of the hypothesis, uniformly.** The `ℂ³` example of B15-S is the
3-point `Set` example: `g(2) = g(3) = 1`, `g(1)` undefined; `g∘g = 0` is pure
(`π_∅ ∘ ζ_1`), `g` merges. Here `im g = {1} ≠ {2,3} = ⌈1∘g⌉`. The same
example lives in `Kl(𝒟)`, `CvNᵒᵖ`, `vNᵒᵖ`, `EJAᵒᵖ` (diagonal `ℝ³`).

**Thm B (`Set`).** With `D := dom g = im g`, `g` maps `D` into `D`, so
`dom(g∘g) = D`. If `g(x) = g(y)` for `x, y ∈ D` then `g(g(x)) = g(g(y))`,
and `g∘g` injective on `D` gives `x = y`. (Only `im g ≤ ⌈1∘g⌉` was used.) ∎

**Thm B (`Kl(𝒟)`).** Write `S_x := supp g(x) = g_⋄({x})`, `D := {S_x ≠ ∅} =
im g`. Purity of `f := g∘g` means: `f_⋄({x})` is an atom for `x ∈ D` and
`x ↦ f_⋄({x})` is injective on `D`. Since `f_⋄ = g_⋄ ∘ g_⋄` preserves joins,
`f_⋄({x}) = ⋃_{y ∈ S_x} S_y`, a single atom `{z}`; each `S_y` (`y ∈ S_x ⊆ D`)
is non-empty, so `S_y = {z}` for all `y ∈ S_x`.
 (i) *No merging*: if `g(y₁), g(y₂)` (`y_i ∈ D`) have the same support `{z}`,
     then `f_⋄({y₁}) = S_z = f_⋄({y₂})`, so `y₁ = y₂`.
 (ii) *No randomness*: by (i) all `y ∈ S_x` coincide, so `S_x` is an atom.
Thus `g(x) = w(x)δ_{φ(x)}` with `φ` injective on `D`: pure. ∎

**What is abstract, what is not.** The lattice half is free in any
⋄-effectus: `(−)_⋄` is functorial and join-preserving (left adjoint in 207III),
so `g_⋄(s) = g_⋄(t) ⟹ f_⋄(s) = f_⋄(t)`; whenever the pure `f` has `f_⋄`
injective (all finite-dimensional examples: `α ∘ asrt_q` with `(asrt_q)_⋄`
invertible for faithful `q`), `g_⋄` is an injective join-map, hence an order
embedding, and `g_⋄ ∘ g_⋄ = f_⋄` onto forces

    g_⋄ is a lattice automorphism of SPred X.                          (†)

The *determinism* half — from (†) to "`g` is pure" — is example-specific:
in `Kl(𝒟)`/`Set` (†) is a permutation and we are done; in `B(H)`, `n < ∞`,
(†) sends atoms to atoms, i.e. with Kraus `g = Σ ad_{A_k}`, all `A_kψ` are
parallel for every `ψ`, which with injectivity gives `A_k = λ_k A_1`
(checked for `M₂`; general `n` plausible). In type I∞/II the input
`f_⋄` injective is *false* (§1, `c_q`), and this is exactly where B15-S needs
the Schur complement of `M₂(g)` (Step A) and the polar phase (Step B).

**No coproduct analogue.** 2-positivity is positivity of `g ⊗ id_{M₂}` on
`𝒜 ⊗ M₂`, a tensor. The effectus coproduct `X + X` only yields `g + g`, whose
positivity is 1-positivity; `M₂(𝒜)` is not an object built from `X` by
effectus operations. So Statement B has no proof from the ⋄/`&` axioms via
`X + X`; the Schur complement has no effectus avatar.

**Conj B.** Statement B holds in every `&`-effectus whose sharp predicates are
atomistic and whose faithful `asrt_q` have `(asrt_q)_⋄` injective (this
includes `EJAᵒᵖ`, where `U_{√q}` is invertible for faithful `q`, provided
"(†) ⟹ pure" is checked there); it holds in `vN` by B15-S; it is *open* for a
general `&`-effectus, and I expect a counterexample in a synthetic one (a
non-atomistic effectus where (R) cannot be recovered from ⋄-data).

## 3. Square roots of pure maps (Thm C in `Kl(𝒟)`; Conj C for `EJAᵒᵖ`)

**Thm C (`Kl(𝒟)`).** A pure endomap `h = w·δ_φ` is ⋄-self-adjoint iff `φ`
restricts to an involution of `D = {w>0}`. Proof: `h^⋄(S) = φ⁻¹(S) ∩ D`,
`h_⋄(S) = φ(S ∩ D)`. At `S = {y}`: if `w(y) > 0` then `φ⁻¹(y) ∩ D = {φ(y)}`,
so `w(φ(y)) > 0` and `φ(φ(y)) = y`; if `w(y) = 0` no `x ∈ D` has `φ(x) = y`.
Conversely an involution of `D` gives equality on singletons, hence on all `S`
by join-preservation. Then `h∘h = asrt_{w·(w∘ϑ)}`. Consequences:
* the pure ⋄-self-adjoint square roots of `asrt_p` are exactly `w·δ_ϑ` with
  `ϑ` an involution of `{p>0}`, `p∘ϑ = p`, and `w(x)w(ϑx) = p(x)`
  (`w = √p` and `ϑ = id` is the canonical one); non-unique, as in `vN`
  (`ad_{√p}∘ϑ`, `ϑ` a symmetry commuting with `p`), so 206II.4's uniqueness is
  a uniqueness of *squares*, not of roots — matching the B15-S repair;
* ⋄-positive = `h∘h` with `h` ⋄-self-adjoint: in `Kl(𝒟)` the eff-notion
  (no purity clause) and the proc-style notion (pure `h`) agree, because every
  ⋄-self-adjoint `h` here is pure: `h^⋄ = h_⋄` forces `φ⁻¹(y) ∩ D` to be an
  atom, i.e. injective *and* the support of `h(x)` to be `{ϑ(x)}`. So in
  `Kl(𝒟)`, unlike `vN` (`ad_{B₁}+ad_{B₂}`), ⋄-self-adjoint ⟹ pure. The `vN`
  gap is a genuinely non-commutative phenomenon (a sum of two conjugations
  with the same sharp footprint).

**Conj C (`EJAᵒᵖ`).** Pure ⋄-self-adjoint endomaps are `U_{√p} ∘ ϑ` with `ϑ`
an involutive Jordan automorphism and `ϑ(p) = p`; every `asrt_p = U_{√p}` has
the root `U_{p^{1/4}}`. The `vN` proof pattern (100III + self-contraposition)
transfers if EJA has (a) Gardner and (b) the polar/phase decomposition for
`U_a`; (b) is unclear for non-special EJAs (Albert algebra).

## 4. Rigid and extreme (Thm D in `Kl(𝒟)`; Conj D)

**Effectus formulation.** `f : X → Y` is **rigid** if `1∘g = 1∘f` and
`g^⋄ = f^⋄` imply `g = f` — "`f` is determined by its total effect and its
⋄-equivalence class" (102II verbatim, since `f^⋄(s) = ⌈f(s)⌉`). `f` is
**extreme** if it is extreme in the convex set `{g : 1∘g = 1∘f}` (needs
convex homsets; 102III: rigid ⟹ extreme in `vN`).

**Thm D (`Kl(𝒟)`).** rigid ⟺ extreme ⟺ deterministic (`g(x) = w(x)δ_{φ(x)}`,
`φ` arbitrary). Deterministic ⟹ rigid: `g^⋄({y}) = f^⋄({y})` pins
`supp g(x) = {φ(x)}` and `1∘g = w` pins the mass. Non-deterministic ⟹ not
extreme (split `f(x) = ½δ₁ + ½δ₂` as `½(δ₁) + ½(δ₂)` on that point, keep the
rest) and not rigid (re-weight to `⅓δ₁ + ⅔δ₂`). Extreme ⟹ deterministic by
the same splitting. ∎ So in `Kl(𝒟)`

    pure  =  rigid  ∧  (no merging: φ injective on D),

and rigidity is exactly condition (R) of §1, *not* purity: `δ_φ` with `φ`
non-injective is rigid, extreme, and impure. This is the clean form of
102IX: pure ⟹ rigid is the inclusion (R)∧(M) ⊆ (R).

**Conj D (`vN`).** `f` is rigid ⟺ `h_f` is nmiu (sharp-preserving). ⟸ is
102V + the 102IX argument with `[f]⁻¹` replaced by factoring `h_f` through its
image (nmiu maps are rigid without injectivity, 102V). ⟹: if `h_f(s)` is
not a projection for some `s`, perturb the Kraus/Stinespring weights as in
the `Kl(𝒟)` re-weighting — plausible, not checked in type II. Extreme ⟹
rigid is **open** in `vN`: Landau–Streater-type extreme unital channels
(spin-1, Kraus rank 3) are candidates for extreme-but-not-rigid.

## 5. Summary and the best conjecture

* Purity decomposes as **rigidity (R) + injectivity (M)** *of the
  normalisation `h_f`*; in `Kl(𝒟)` this is a theorem with rigid = extreme =
  deterministic, in `vNᵒᵖ` it is Gardner + a lattice argument. (Thm A.)
* The B15 theorem is a `Set`/`Kl(𝒟)` triviality and a `vN` theorem, with
  the *same* necessity example in every effectus. Its lattice half (no
  merging) is abstract; its determinism half is not, and the Schur complement
  has no `X + X` avatar. (Thm B / Conj B.)
* Pure ⋄-self-adjoint maps are "weight × involution" everywhere checked;
  square roots of `asrt_p` are never unique. (Thm C.)
* **Best conjecture (B′).** In an `&`-effectus with atomistic sharp
  predicates and `(asrt_q)_⋄` injective for faithful `q`: an endomap `g` with
  `im g = ⌈1∘g⌉` whose square is pure has `g_⋄` a lattice automorphism (†);
  and `g` is pure iff moreover `g_⋄` sends atoms to atoms. In `vN` of type I∞
  the first hypothesis fails and (†) is *false* for pure `c_q`, which is why
  the Schur complement was unavoidable there.
