# Adversarial review of `B15-S.md`

**Verdict: the Theorem is CERTIFIED; the *Conclusion paragraph* is FALSE as
stated and needs one named repair (re-import self-contraposition).** Steps A
and B survive every attack below. Two remarks (Kraus, Lean cost) have defects.

Read against proc.tex directly: 98I/98II (`dfn-standard-corner-and-filter`,
`filter-basic`, :551/:577), 98IX (`square-f`, :707), 98XI (`ad-pure`, :730),
99II (`gardner`, :795), 99IX (`iso`, :874), 100I–100III (:925–1015),
100VII (`special-pure-maps`, :1016), 101I/101VI (:1030 ff.), 103I/103III
(:1388), 105V (`positive-map-uniqueness`, :1785); carrier = *least* `e` with
`f(e^⊥)=0`, and `⌈f⌉=1 ⟺ f` faithful (vn.tex:3042/:3053.3).

## Setting — CORRECT

`⌈g⌉=⌈g(1)⌉=e` alone gives everything claimed: `g(x) ≤ ‖x‖g(1)` puts
`g(𝒜) ⊆ e𝒜e`, so `g` restricts to `M := e𝒜e`; there `⌈g⌉ = 1` (faithful),
hence `⌈f⌉ = ⌈g∘g⌉ = 1`, and `⌈f(1)⌉ = ⌈g(p)⌉ = ⌈g(⌈p⌉)⌉ = ⌈g(1)⌉ = 1` by
`ncp-ceil`. `f` pure on `𝒜` with `⌈f⌉ ≤ e` gives `f = f|_M ∘ π_e`, so
`[f|_M] = [f]` and `f|_M` is pure by 100III. Note: **no self-contraposition
is used here**, unlike `B15-elementary.md` §1, which derived `⌈f⌉=⌈f(1)⌉`
from `f^⋄ = f_⋄`. The weakening is legitimate.

`γ := [g] : M → M` is ncp, **unital and faithful** by 98IX — exactly what
Step A needs; `g = c_p ∘ γ` since `⌈g⌉ = ⌈p⌉ = 1`. `f` faithful+pure ⟹ filter
(100VII.1) ⟹ `f = c_q ∘ ϑ` with `ϑ = [f]` ncpu-iso (98II.1) hence **nmiu**
(99IX). Since `⌈f⌉ = 1` there is no corner in the way: `ϑ` is defined on all
of `M`, so `ϑ(s)` is a projection for **every** projection `s ∈ M`. Attack
(2) fails: `f(s) = √q·proj·√q` is justified for every `s`, not just in a
corner.

## Step A — CORRECT

* `[[1,s],[s,s]] = W₀*W₀ ≥ 0` for `W₀ = [[1,s],[0,0]]`: verified entrywise
  (`(2,2) = s² = s`). `M₂(γ)` positive since `γ` is cp (34IV `cp_iff`,
  `A/CStar/Matrices.lean:2151`). Schur complement of the invertible corner
  `γ(1) = 1` gives `C ≥ B*A⁻¹B`, i.e. `γ(s) ≥ γ(s)²`: **direction correct**,
  `D ≥ 0`.
* `N = W*W` for `W = [[√p, γ(s)√p],[0,0]]`: verified entrywise —
  `(1,1)=p`, `(1,2)=(2,1)=√p γ(s)√p = y` (self-adjoint, so `y* = y` is not a
  typo), `(2,2)=√p γ(s)²√p = Ψ`. So `N ≥ 0` unconditionally.
* `M₂(g)` applied entrywise, `g(p) = g(g(1)) = f(1) = q`, `g(y) = f(s)`. ✓
* Regularised Schur: `diag(ε,0) ≥ 0` keeps positivity, `q+ε` invertible, so
  `f(s)*(q+ε)⁻¹f(s) ≤ g(Ψ)`. With `f(s) = √q t √q`, `t = ϑ(s)` a projection,
  the LHS is `√q t·q(q+ε)⁻¹·t√q`; `q(q+ε)⁻¹ ↑ ⌈q⌉ = 1`, and `b*(·)b` is
  normal, so the sup is `√q t² √q = f(s)`. **(3) holds.**
* Squeeze: `f(s) = g(Ψ) + g(√pD√p)` and `f(s) ≤ g(Ψ)` force
  `g(√pD√p) = 0`. Faithfulness of `g` **on `M`** is `⌈g|_M⌉ = 1`, which is
  the hypothesis `⌈g⌉=⌈g(1)⌉` transported (above) — established, not
  assumed. Then `√pD√p = 0 ⟹ D^{1/2}√p = 0 ⟹ D^{1/2}⌈p⌉ = D^{1/2} = 0`
  since `⌈p⌉ = 1`, where `p = g(1) = γ`'s filter weight. `D = 0`. ✓
* `γ(s)` a projection for all `s`, `γ` ncpu ⟹ multiplicative by 99II
  (4)⟹(1); `γ` positive ⟹ `*`-preserving; normal. `γ` is nmiu. ✓

Sanity check: for the non-pure `g = (tr/2)·1` on `M₂` the chain breaks
precisely at "`t` is a projection", and (3) degrades to the true `¼ ≤ ¼`.

## Step B — CORRECT

`γ` nmiu ⟹ `γ(√p) = √γ(p) = √ρ` ⟹ `γc_p = c_ργ`; `⌈ρ⌉ = γ(⌈p⌉) = 1` by
99II(5). `c_p c_ρ = ad_a`, `a = √ρ√p`, and `a*a = √pρ√p = f(1) = q`,
`aa* = √ρ p √ρ` with `⌈aa*⌉ = ⌈ρ⌉ = 1`. `⌈ad_a⌉ = ⌈aa*⌉ = 1`, so `ad_a` is
pure (100II.3) **and faithful** ⟹ filter (100VII.1). By 98XI,
`β = [ad_a] = [a](·)[a]*` is an ncpu-iso `⌈aa*⌉M⌈aa*⌉ → ⌈a*a⌉M⌈a*a⌉ = M → M`
— note 98XI already asserts this, so the unitarity of `[a]` is a true but
*redundant* remark, not a load-bearing step. Uniqueness in 98IX (or just
injectivity of `c_q`) gives `ϑ = β∘γ²`. Domains and codomains all match `M`,
so `γ² = β⁻¹ϑ` is onto `M` and `ran γ ⊇ ran γ² = M`: **γ surjective**.
`γ` nmiu + faithful ⟹ injective, so `γ` is an nmiu-automorphism, and 100III
(3⟹1) makes `g` pure. Attack (3) fails.

## Conclusion paragraph — **FALSE as stated** (repairable)

103I.1 defines ⋄-self-adjoint as *pure **and** contraposed to itself*. The
boxed Theorem assumes only `⌈g⌉=⌈g(1)⌉`, and 103III.1 runs the *other* way
(⋄-self-adjoint ⟹ `⌈g⌉=⌈g(1)⌉`). So "Being pure and contraposed to itself"
is not available, and the final display is false:

> `𝒜 = M₂`, `u = diag(1,i)`, `g = ad_u`. Then `⌈g⌉ = ⌈g(1)⌉ = 1`,
> `f = g∘g = ad_{diag(1,-1)}` is pure, `q = f(1) = 1` — but
> `f ≠ √q(·)√q = id` (it flips the sign of off-diagonals). Indeed
> `g^⋄(e) = u*eu ≠ ueu* = g_⋄(e)`, so `g` is not self-contraposed and `f` is
> not ⋄-positive.

**Repair (necessary, and sufficient):** state the last paragraph under the
extra hypothesis `g^⋄ = g_⋄`, which is what the B15 application supplies and
which the document's own preamble admits ("again at the very end"). Under it
the paragraph is correct. The Theorem itself (`g` pure) is untouched.

## `su_exists_asrt` claim — **FALSE** (misidentified declaration)

`su_exists_asrt` (`B/Eff/VNExamples.lean:4813`) carries **no `sorry`**; it is
the *existence* half and is fully proved. The single `sorry` in that file is
`vn_is_andthen_eff:9392`, discharging hypothesis `H` of
`su_andThenEffectus_of_pure_sqrt:5473`:
`∃ h, IsPure h ∧ DiamondSelfAdjoint h ∧ g≫g = h≫h`. `h := g` does work — the
document's substantive claim is right — but note `IsPure` there is *effectus*
purity, so the discharge also needs `su_isPure_of_procPure:5103` (present).
Line refs otherwise check out: `square_f`:2911, `gardner`:3405, `iso`:3428,
`isPure_adSelf`:4112, `pure_fundamental`:4430, `special_pure_maps_1`:4499,
`polar_decomposition`:3335, 104IX at :8400 (`positive_map_uniqueness` is at
:8962, not stated).

## Minor items

* **Necessity example — CORRECT.** `g(x)=(x₂+x₃,0,0)` on `ℂ³`: `g∘g = 0`,
  pure (`c_0∘π_0`); `⌈g⌉=(0,1,1) ≠ (1,0,0)=⌈g(1)⌉`; `[g] : ℂ²→ℂ` is not
  injective, so `g` is impure by 100III.
* **"(S) is false for `g = c_p`" — CORRECT.** `c_p` is self-contraposed,
  `⌈c_p⌉=⌈p⌉=1`, `c_p∘c_p = ad_p` pure, and `√pM√p ⊊ M`. The route-(a)
  remark is a correct restatement of the same fact.
* **Kraus cross-check — GAP in scope, sound in content.** "in type I write
  `g = Σ ad_{A_k}`" is **false for general type I**: on `ℂ²` the nmiu swap
  has no Kraus form inside `ℂ²`. Read it as `𝒜 = B(H)`. The algebra is
  right: `A_kA_l = c_{kl}W`; `Cμ = 0 ⟹ ran(Σμ_lA_l) ⊆ ⋂ker A_k = 0` gives
  **injectivity** of `C` (say "injective", not "invertible", for infinite
  families — injective + rank 1 is all that is used); associativity gives
  `c_{lm}A_kW = c_{kl}WA_m`, hence column `m` `= λ_m·`row `k₀`, `rank C ≤ 1`.
  "Either way `dim V = 1`" should read `≤ 1`: the degenerate branch yields
  `W = 0`, i.e. `g = 0`, already discarded.
