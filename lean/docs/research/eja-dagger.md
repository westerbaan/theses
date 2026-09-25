# `EJAᵒᵖ` as an `&`-effectus and a `†`-effectus — research note (2026-09-12)

> **Correction (2026-09-26).** §1 step 1 repeats EJA Lemma 38's broken step ("Θ(q) = q"); EJA 38 is false as printed (`papers/ERRATA.md`, `docs/research/review-eja38.md`).  The conclusion `g = U_{√p}` survives under the repaired Lemma 38′ with `p = (q·Θq)²`, but the argument given below does not establish it.


Sources: eff.tex 211II (`&`-effectus, line 4792), 211IV (line 4859), 215I/215III
(`dagger-theorem`, 5282/5310), 215VI.61–72 (the vN dagger, 5344), 215VII (5398:
axiom 2 "is essentially the fundamental formula"), 216V/216VII, 217II
(`dagger-definition2`); proc.tex 105V (`positive-map-uniqueness`, 1772),
104IX (faithful case, 1634); [eja] = Westerbaan–Westerbaan–van de Wetering,
*Pure maps between EJAs*, EPTCS 287 (2019) 345–364 (arXiv 1805.11496).
Tree: `Theses/B/Eff/JordanAlgebras.lean` (6,217 lines, 2026-09-05).
Conventions: maps are written in the *algebra* direction `V → W`; `U_a = 2L_a² − L_{a²}`
(`ejaU`), `P₁(e) = U_e` for an idempotent (`ejaU_idem`), `V₁(e)` the corner (`EJACorner`).

## 0. What the tree has (and deliberately does not)

* `eja_U_nonneg'`: `U_a` positive for **every** `a`; `ejaB_U_self_adj`: `U_a` is
  trace-form self-adjoint; `ejaU_apply_one : U_a 1 = a²`; `ejaU_one`.
* `eja_U_family_comp'` (**one-family law**): for `a = Σ g(l) e_l`, `b = Σ g'(l) e_l`
  over one spectral family, `U_a U_b = U_{ab}`. Hence `U_b U_b = U_{b²}`, `U_{√p}² = U_p`,
  `U_a`, `U_b` commute, and `U_{b'} U_b = P₁(⌈b⌉)` (`eja_exists_filter`).
* `eja_U_half_zero`: `U_a y = 0` for `a ∈ V₀(c)`, `y ∈ V½(c)`; `eja_U_split`/`eja_U_split'`.
* `eja_exists_nonneg_sqrt` (existence only; no uniqueness lemma yet).
* Effectus layer: `ejapsuHasQuotients` (`ξ_p = U_{√(pᗮ)} : V₁(⌈pᗮ⌉) → V`),
  `ejapsuHasComprehension` (`π_p = P₁(⌊p⌋) : V → V₁(⌊p⌋)`), images = support
  idempotents, `ejapsu_isSharp_iff` (sharp = idempotent), `diamond_effectus_eja`,
  `Par EJAᵒᵖ` real effectus.
* **Not** in the tree, by design: the fundamental formula `U_{U_a b} = U_a U_b U_a` (FF),
  inverses of general elements, any topology. `Aut`/Jordan-isomorphism theory absent.

## 1. `EJAᵒᵖ` is an `&`-effectus with `asrt_p = U_{√p}`

**211II.1, existence.** `U_{√p}` is pure: `U_{√p} = ξ_{pᗮ…}∘π` as in [eja] p. 352 — the
standard filter of `p` after the standard corner of `⌈p⌉` is `U_{√p} P₁(⌈p⌉) = U_{√p}`
(`√p ∈ V₁(⌈p⌉)`, so `U_{√p}` kills `V½ ⊕ V₀` of `⌈p⌉`: the mirror image of
`eja_U_half_zero`). It is `⋄`-positive: `U_{√p} = U_{p^{1/4}} ∘ U_{p^{1/4}}` (one-family law),
and `U_a` is `⋄`-self-adjoint for every `a` because it is trace-form self-adjoint
([eja] Prop. 33: `⟨f^⋄(s), t⟩ = 0 ⟺ ⟨s, f^⋄(t)⟩ = 0` for idempotents `s, t`, using
`⌈q⌉ ⊥ s ⟺ B(q, s) = 0` for `q ≥ 0`). Only tree-level facts. `1∘U_{√p} = U_{√p} 1 = p`.

**211II.1, uniqueness — the Jordan proof** ([eja] Lemma 38, Prop. 39, Thm 34; the vN
analogue is 105V through 104IX + `centrally-similar`). Let `g` be pure, `⋄`-positive,
`g = f∘f` with `f` `⋄`-self-adjoint, `g(1) = p`.
1. *Faithful case* (`im g = 1`, so `im f = 1`, `⌈f(1)⌉ = 1`, `q := √f(1)` invertible).
   `f` pure ⇒ `f = ξ ∘ Θ' ∘ π` with `ξ` a filter, `π` a corner; faithful+`⋄`-self-adjoint
   force `π = id`, `ξ = U_q` up to iso, so `f = U_q ∘ Θ` for a *unital order iso* `Θ`.
   Unital order isos of EJAs are Jordan isos ([eja] Prop. 36: idempotents = order-sharp
   effects, tree `ejapsu_isSharp_iff`; orthogonality `e ≤ f^⊥` is order-theoretic; then
   `Θ(a)² = Θ(a²)` via the spectral decomposition). Hence `Θ U_a Θ⁻¹ = U_{Θa}`.
   `⋄`-self-adjointness `⟨f(a), b⟩ = 0 ⟺ ⟨a, f(b)⟩ = 0` gives `⌈U_qΘ(a)⌉ = Θ⁻¹⌈U_q a⌉`;
   evaluated at the primitive idempotents `q_i` of `q = Σ λ_i q_i` this yields
   `Θ(q) = q` (an eigen-decomposition matching argument, [eja] p. 356), whence
   `Θ` commutes with `U_q`, and `g^⋄ Θ^⋄ = g^⋄ (Θ⁻¹)^⋄` with `g^⋄` injective on
   idempotents gives `Θ = Θ⁻¹`. Then `g = U_qΘU_qΘ = U_q U_{Θq} Θ² = U_q² = U_{q²}`
   (one-family law), and `p = g(1) = q⁴`, so `g = U_{√p}`.
2. *General case*: corestrict along `im g = ⌈p⌉` (comprehension universal property,
   tree has it); `ḡ` is faithful, pure, `⋄`-positive on `V₁(⌈p⌉)`, so `ḡ = U_{√p}` there,
   and `g = U_{√p} P₁(⌈p⌉) = U_{√p}`.
   **"Pure" in EJAs**: every pure `φ : V → W` is `φ = U_{√φ(1)} ∘ Θ ∘ P₁(⌈φ⌉)` with
   `Θ : V₁(⌈φ⌉) ≅ V₁(⌈φ(1)⌉)` a Jordan iso — the exact analogue of 215VI.61
   `φ = √φ(1) ϑ(⌈φ⌉·⌈φ⌉) √φ(1)`; the role of "inner ad_V" is played by `U_b`, the
   role of `ϑ` by a Jordan iso (in `M_n(ℂ)^{sa}`: `ad_u` or `ad_u∘transpose`).
   *No FF is used anywhere in uniqueness*: only the one-family law, spectral theory of
   one element, primitive idempotents (`EJAPrimitive`), and Jordan-iso bookkeeping.
   **B15 recurs verbatim**: as in `su_andThenEffectus_of_pure_sqrt`, both 105V and
   [eja] Thm 34 assume the `⋄`-self-adjoint square root `f` is *pure* (step 1 factors
   `f`); eff.tex 206II.4 does not. `U_b` for a non-positive `b` is `⋄`-self-adjoint with
   `U_b² = U_{b²} = U_{|b|}²`, so the pure case is consistent; the impure case is open
   for EJAs exactly as for vN. Formalise under the same hypothesis `H`, or settle B15.

**211II.2 (`ξ∘π` pure = polar decomposition, 211II.31).** [eja] Thm 27/Prop. 30: for an
idempotent `e` and effect `q`, `P₁(e) ∘ U_{√q} = U_{√a} ∘ Φ ∘ P₁(t)` with
`a = U_e q` (`= q & e` read in `V₁(e)`), `t = ⌈U_{√q} e⌉`, and `Φ = U_{a^{-1/2}} P₁(e) U_{√q}`
restricted. The tree gives `Φ` by the filter universal property (`Φ` unital), and the
corner factorisation through `t = im Φ`. What needs FF is only that `Φ` is an *iso*:
* `ΦΦ* = U_{a^{-1/2}} P₁(e) U_q P₁(e) U_{a^{-1/2}} = U_{a^{-1/2}} U_{U_e q} U_{a^{-1/2}} = P₁(⌈a⌉)`:
  uses **FF at an idempotent** `U_e U_b U_e = U_{U_e b}` and the one-family law only;
* `Φ*Φ = id_{V₁(t)}`: [eja] argue via `im Φ* = t`, using FF at `(√q, ·)` — the
  **general** FF. (A rank argument might avoid it: `ΦΦ* = id` gives `Φ` onto and `Φ*`
  injective; equality of `dim V₁(t)` and `dim V₁(⌈a⌉)` would finish. Not checked.)
**FF at an idempotent is cheap**: for `x ∈ V₁(e)` and `b = b₁ + b½ + b₀` (Peirce),
`P₁(e) U_b x = U_{b₁} x` reduces by the Peirce multiplication rules to the single identity
`2 P₁(z(zx)) = P₁(z² x)` for `z ∈ V½(e)`, `x ∈ V₁(e)` (an instance of `eja_lin`), plus
`U_{b₁}` vanishing on `V½(e) ⊕ V₀(e)` (mirror of `eja_U_half_zero`). Checked in `M₂(ℝ)^{sa}`.
**Reduction of the general FF to the two-valued case** (new, tree-native): FF holds for
`a` if it holds for `a₁ = l c + (1−c)` (two-valued at an idempotent `c`, all `b`) and for
`a₂ = c + a'` with one fewer non-unit spectral value: `U_a = U_{a₁} U_{a₂}` (`eja_U_split`),
`U_{a₁}, U_{a₂}` commute (one family), so `U_a U_b U_a = U_{a₁} U_{U_{a₂} b} U_{a₁} = U_{U_a b}`.
By homogeneity the two-valued case is `a = 1 + s c`: with `U_{1+sc} = id + 2s L_c + s² P₁(c)`,
the identity splits into the `s¹…s⁴` coefficients; `s¹` (`L_c U_b + U_b L_c = 2 U_{b, cb}`)
follows from `[L_c, L_{b²}] = 2[L_{cb}, L_b]` and `L_{b(bc)}`-expansion (both `eja_lin`
instances; checked by hand), `s⁴` is FF at the idempotent `c`, `s², s³` are the remaining
Peirce identities. This is Macdonald-free and matches the tree's induction style
(`eja_U_nonneg_family`, `eja_U_family_comp`). Alternative: van de Wetering,
arXiv 1807.00164, an explicit chain of linearised Jordan identities.

## 2. `EJAᵒᵖ` is a `†`-effectus by 215III (the tree's `dagger_theorem` route)

Axiom (1): `q & q = q ∘ asrt_q = U_{√q} q = q²` (one family), so (1) is *unique positive
square root of an effect* — spectral: existence is `eja_exists_nonneg_sqrt`; uniqueness
needs `eja_sqrt_unique` (if `b² = b'² = p`, `b, b' ≥ 0`, then `b = b'`: `b` lies in the
associative subalgebra of `p`, i.e. `b = Σ √λ e_λ`; ~150 lines).
Axiom (2): `asrt²_{p&q} = asrt_p asrt²_q asrt_p` reads `U_{U_{√p} q} = U_{√p} U_q U_{√p}`
(both sides via the one-family law: `U_{√(p&q)}² = U_{p&q}`, `U_{√q}² = U_q`). This **is**
FF at `(√p, q)` for effects `p, q`; since FF is polynomial in `a`, linear in `b`, and
effects span with non-empty interior, axiom (2) ⇔ the full FF. 215VII says as much.
Nothing weaker suffices: (2) at `p` sharp is FF at an idempotent (§1, cheap); (2) in
general is the whole formula.
Axiom (3): the quotient of an idempotent `s` is `ξ_s = U_{√s} = U_s` corestricted to
`V₁(s)`, i.e. the *inclusion* `V₁(s) ↪ V`; it sends idempotents to idempotents, so `t∘ξ_s`
is sharp for sharp `t` (`ejapsu_isSharp_iff`). Immediate. (215VI's vN proof needs
`sharp-multiplicative`; here the inclusion is a Jordan homomorphism on the nose.)
So: `EJAᵒᵖ` is a `†'`-effectus given `&`-effectus + `eja_sqrt_unique` + FF, and a
`†`-effectus by the abstract `dagger_thm_sufficiency`.

## 3. The dagger on `Pure(EJAᵒᵖ)` concretely

By 217II and the standard form (`φ = U_{√φ(1)} ∘ Θ ∘ P₁(⌈φ⌉)`):
`φ†(b) = ι_{⌈φ⌉}(Θ⁻¹(U_{√φ(1)} b))`, i.e. `asrt_p† = asrt_p` (`U_{√p}† = U_{√p}`),
`(P₁(e))† = ι_e` (corner ↔ inclusion, 216VII `ζ_s† = π_s`), `Θ† = Θ⁻¹` (216IX). Since `U_a`
and `P₁(e)` are trace-form self-adjoint (`ejaB_U_self_adj`, `ejaB_pone_self_adj`) and a
Jordan iso is a trace-form isometry (`τ(Θx) = tr L_{Θx} = tr(Θ L_x Θ⁻¹) = τ(x)`), **the
dagger is the trace-form adjoint** — [eja] §4 defines it that way; 215VI.72's remark for
finite-dimensional vN algebras is the general rule here, EJAs being finite-dimensional.
For `Herm_n(ℂ)` it specialises to `ad_T ↦ ad_{T*}` (215VI.72), for `Herm_n(ℝ)` to
`ad_T ↦ ad_{Tᵀ}`, for spin factors to the Lorentz adjoint on `ℝ ⊕ H`.

## 4. When are two comprehensions `{p}`, `{q}` of sharp predicates "equivalent"?

**The `†`-intrinsic relation.** In `Pure C` call `f` a `†`-partial isometry if `f f† f = f`.
Define `p ≃ q` iff some `f : X → X` in `Pure C` has `f†f = asrt_p`, `ff† = asrt_q`.
* In `vNᵒᵖ`: `f f† f = f` forces `f(1)` sharp, so `†`-partial isometries are exactly
  `f(a) = ϑ(sas)` with `ϑ : s𝒜s ≅ t𝒜t` nmiu; hence `p ≃ q ⟺ p𝒜p ≅ q𝒜q` as vN algebras —
  *abstract corner isomorphism*, strictly weaker than MvN: `𝒜 = ℬ ⊕ ℬ`, `p = (1,0)`,
  `q = (0,1)` (central, `p ≁ q`, corners isomorphic via the flip); the hyperfinite `R`
  (every non-zero corner `≅ R`, so all `p ≃ q`, while `p ~ q ⟺ τ(p) = τ(q)`); any
  commutative algebra (`p ~ q ⟺ p = q`, but `ℓ^∞(P) ≅ ℓ^∞(Q) ⟺ |P| = |Q|`). The obstruction
  is always an *outer* iso of corners; on `B(H)` (all automorphisms inner) `≃` = MvN.
* In `EJAᵒᵖ`: `p ≃ q ⟺ V₁(p) ≅ V₁(q)` as EJAs. In a simple EJA this is `rank p = rank q`
  (the rank of `V₁(p)` is `rank p`), which is also `Aut(V)`-conjugacy — so for simple EJAs
  `≃` is the Jordan MvN analogue; in `⊕ V_i` it again ignores swaps of isomorphic summands.
* In `Kl(𝒟)`/`CvNᵒᵖ`: `p ≃ q ⟺ |p| = |q|` (a bijection of subsets), MvN is equality.
**A relation that does recover MvN, expressible in a real `&`-effectus.** For a sharp `g`
the map `L_g := asrt_g ⋁ asrt_{g⊥}` is the "measure `g` and forget" side-effect (211III).
Call an automorphism `σ` of `X` a **symmetry through `g`** if `½ id ⋁ ½ σ = L_g`. In `vNᵒᵖ`
this forces `σ = ad_{2g−1}` (a self-adjoint unitary), in `EJAᵒᵖ` `σ = U_{2g−1} = P₁ − P½ + P₀`
(positive by `eja_U_nonneg'`, an involutive Jordan automorphism); in `CvNᵒᵖ` `σ = id`.
Define `p ≈ q` iff a finite chain of symmetries carries `p` to `q` (`σ_⋄ p = q`). This is
Topping's / Alfsen–Shultz's equivalence of projections in JBW-algebras; in `vNᵒᵖ`
`≈` = "exchanged by a product of symmetries" = unitary equivalence (Fillmore), which is
MvN for *finite* algebras (`R`: `τ(p) = τ(q)` ✓; `ℬ ⊕ ℬ`: summands preserved ✓; commutative:
equality ✓) and for general `𝒜` is MvN of `p ⊕ 0`, `0 ⊕ q` in `M₂(𝒜)` — MvN itself needs
the qubit tensor (`p ⊥ q`, `p ~ q ⟺ {p ∨ q} ≅ M₂ ⊗ {p}` over the diagonal corners), which
`EJAᵒᵖ` lacks. Proposal: record `≃` (the `†`-notion) and `≈` (symmetries) as two distinct
effectus relations; `≈ ⊆ ≃`, equal on `B(H)` and on simple EJAs (`U_{2g−1}` products
generate `Inn(V)`, transitive on idempotents of fixed rank), different elsewhere.

## 5. Costed list: "`EJAᵒᵖ` is an `&`-effectus" (and `†'`) on top of the tree

| # | item | est. lines | risk |
|---|------|-----------:|------|
| 1 | `eja_U_half_zero'`: `U_c y = 0` for `c ∈ V₁(e)`, `y ∈ V½(e)`; `U_c V ⊆ V₁(⌈c⌉)` | 120 | low |
| 2 | `U_{√p}` pure: `ξ_p ∘ π_{⌈p⌉} = U_{√p}` with the tree's `ejapsu` quotient/comprehension | 250 | low |
| 3 | `U_a` `⋄`-self-adjoint from trace-form self-adjointness (`⌈q⌉ ⊥ s ⟺ B(q,s)=0`) | 300 | low |
| 4 | existence half of `existsUnique_asrt` (`U_{p^{1/4}}² = U_{√p}`, items 2–3) | 150 | low |
| 5 | unital order iso ⇒ Jordan iso ⇒ `Θ U_a Θ⁻¹ = U_{Θa}`, `Θ⌈a⌉ = ⌈Θa⌉`, atoms | 500 | med |
| 6 | standard form of a pure map of `EJAᵒᵖ` from the abstract 212III + items 1, 5 | 300 | med |
| 7 | uniqueness (Lemma 38/Prop 39/Thm 34): the `Θ(q) = q` matching argument | 700 | med–high |
| 8 | B15: pure square root hypothesis `H` as in `su_andThenEffectus_of_pure_sqrt` (or settle) | 0 / open | — |
| 9 | FF at an idempotent `P₁(e) U_b P₁(e) = U_{U_e b}` (Peirce computation) | 400 | low–med |
| 10 | polar decomposition / `quot_after_compr_pure`: `Φ` iso (needs 9 and either the general FF or a rank argument) | 800 | med–high |
| 11 | general FF via the two-valued reduction (`s²,s³` Peirce identities + induction) | 1,500–2,500 | high |
| 12 | `eja_sqrt_unique` | 150 | low |
| 13 | `DaggerPrimeEffectus` instance: (1) from 12, (2) from 11 at `(√p, q)`, (3) inclusion sharp | 300 | low |
Total `&`-effectus: ≈ 3,500 lines (items 1–10) + 11 if the rank argument fails; `†'` adds
≈ 450 on top of 11. Item 11 is the block the tree has avoided so far; items 7 and 10 are
the mathematically delicate ones and should get an adversarial review before Lean.
