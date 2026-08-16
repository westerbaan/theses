# `Theses/A/VN/` — full survey of the remaining `sorry`s (worker 75, session 50)

**Headline count: A/VN has 55 code `sorry`s** after session 50 (was 62).
Per file, compiler-counted (`declaration uses 'sorry'` warnings, *not* grep):

| file | sorries |
|---|---|
| `Basic.lean` | 24 |
| `Projections.lean` | 17 |
| `Division.lean` | 7 |
| `NormalFunctionals.lean` | 5 |
| `Completeness.lean` | 2 |
| **total** | **55** |

Refresh with (bypasses another agent's `lake build` lock):

```sh
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
for f in Basic Projections Division NormalFunctionals Completeness; do
  echo -n "$f: "; env LEAN_PATH="$LP" lean Theses/A/VN/$f.lean 2>&1 |
    grep -c "declaration uses"
done
```

> **Session 50 headline — the 890 chain is finished.** **89XI**.1/.2/.3
> (`functional_permanence_*`) and **89XII** (`functional_extension`) are
> proved and axiom-clean.  The "one 120–150 line lemma" the previous session
> expected (*a square-summable family of vectors defines an np-functional on
> `B(H)`*) **already existed, upstream**: it is **38IV**.2
> `bh_functional_lemma_2` in `A/CStar/TowardsVN.lean`, in the same file as
> its converse 39IX `bh_np`, and fully proved.  89XI.1 is 20 lines on top of
> it.  An arbitrary-index wrapper `exists_sumVectorNP` was added to
> `A/VN/NormalFunctionals.lean` for `A/Proc` (see below).

Classification used below: **[S]** self-contained (all ingredients in the
tree), **[B]** blocked on a named `sorry`, **[L]** cited to the literature or
needs a carrier/development Mathlib lacks, **[F]** known false / parked.

---

## `NormalFunctionals.lean` — 5

| line | point | decl | class |
|---|---|---|---|
| 818 | **86XI** | `polar_decomposition_of_functional` | [S] the substantial one; thesis proof at vn.tex:6410ff |
| 830 | **86XII** | `uwcont_on_ball` | [B] on 86XI (it is its corollary) |
| 889 | **87III** | `predual_complete` | [S] operator-norm completeness of the ultraweakly continuous functionals |
| 898 | **87VI** | `norm_predual` | [S] `‖a‖ = sup{|f(a)| : f ∈ (A_*)₁}` |
| 3336 | **90II**.2 | `vn_center_separating_fundamental_2` | [S] norm-density of the finite sums `∑ ωₖ(sₖ*(·)sₖ)`; 90II.1 is proved |

Everything else in the file is proved, including the whole 880–890 block
(88IV–88IX, 89I–89IX, 89XI, 89XII).

## `Completeness.lean` — 2

| line | point | decl | class |
|---|---|---|---|
| 3871 | **77V** | `vn_extension` | [S] ultraweakly continuous extension from an ultraweakly dense ∗-subalgebra |
| 3883 | **77V** | `vn_extension_norm` | [B] on 77V (it takes the extension as a hypothesis, so it is separable, but the argument is the same) |

## `Division.lean` — 7

| line | point | decl | class |
|---|---|---|---|
| 766 | **79VI**.4 | `pseudoinverse_basic_2'_4` | **[F]** false as stated; refutation `pseudoinverse_basic_2'_4_is_false` sits just above it, ERRATA filed, awaiting author |
| 779 | **79VI**.5 | `pseudoinverse_basic_2'_5` | [S] concrete: `(0,0,1,½,⅓,…)` is not pseudoinvertible in `ℓ^∞(ℕ)` — cheapest item in the file |
| 2494 | **81VIII**.2 | `sequential_quotient_2` | [S] uniqueness + ultraweak convergence of `∑_{m,n} tₘ a tₙ`; 81VIII.1 is proved |
| 2581 | **81IX** | `div_usc` | **[F]** second conjunct false (counterexample in the doc comment), ERRATA filed |
| 3040 | **84II** | `fdcstar` | [L] Artin–Wedderburn for finite-dimensional C\*-algebras; large |
| 3074 | **84bIII** | `hereditarilyAtomic_subalgebra` | [S] but real work |
| 3084 | **84bV** | `ha_equalisers` | [B] on 47V `vn_equalisers` (**now proved**, session 50) + 84bIII |

**Note for the next worker:** 84bV's chief ingredient, "the equaliser of two
nmiu-maps is a von Neumann subalgebra", is 47V and was proved this session,
so 84bV is now only blocked on 84bIII.

## `Projections.lean` — 17

| line | point | decl | class |
|---|---|---|---|
| 1693 | **56XVII**.3 | `ceil_supremum_3` | [S] counterexample `1, ½, ⅓, …`; needs a `Nontrivial` witness built by hand |
| 1930 | **58IV** | `ceil_sequential_product` | [S] `⌈pqp⌉ = p ∩ (p^⊥ ∪ q)` |
| 2182 | **59VII**.1–2 | `hilb_ceil_1` | [S] `⌊T⌉`/`⌈T⌋` as range/support projections on a Hilbert space |
| 2191 | **59VII**.3 | `hilb_ceil_2` | [S] `⌊T⌋` for an effect is the projection onto `{x | Tx = x}` |
| 2736 | **62I** | `ncpsu_floor` | [S] `⌊f(a)⌋ = ⌊f(⌊a⌋)⌋`; the thesis's proof cites `cp-cs` (erratum 620.20) |
| 2924 | **63III**.2 | `carrier_ad_operator` | [S] Hilbert-space form of `carrier_ad`, which **is** proved right above it |
| 2989 | **63IV** | `cp_comprehension` | [S] **best next target**: the thesis's proof (vn.tex:3113) reduces to `B = ℂ` by `states_order_separating_1/2` (proved, `A/CStar/Positive.lean:2948/2979`) and then applies Kadison's inequality `omega_norm_basic_1` (proved, `A/CStar/Representation.lean:468`) |
| 3818 | **66IV**.4 | `ultracyclic_basic_4` | [S] Zorn over orthogonal families of ultracyclic projections; 66IV.1/.2/.3 are all proved |
| 3836 | **67II**.3 | `central_examples_3` | [S] only scalars are central in `B(H)` — commute with `|x⟩⟨y|` |
| 3846 | **67IV**.1 | `central_projections_sums_1` | [S] the corner `cA` of a central projection |
| 3862 | **67IV**.2 | `central_projections_sums_2` | [B] on 67IV.1 |
| 4444 | **69II** | `weakly_closed_ideal` | [S] weakly closed two-sided ideals are `cA`; substantial |
| 4861 | **69V** | `proto_gns_ceil` | [S] `⌈⌈ω⌉⌉ = ⌈ρ_ω⌉` |
| 4875 | **69VII** | `gns_ceil` | [B] on 69V |
| 4999 | **69IX** | `vn_center_separating` | [B] on 69VII (the TFAE's (1)⇔(3) is exactly 69VII) |
| 5015 | **70II** | `central_projection_central_carrier` | [B] on 69IX + 66IV.4 |
| 5032 | **70III** | `cvn` | [B] on 70II; also needs 54XI |

The parsec 690–700 block is one chain: **69V → 69VII → 69IX → 70II → 70III**.
Proving 69V unlocks five statements, and it is the highest-return item in
this file.

## `Basic.lean` — 24

| line | point | decl | class |
|---|---|---|---|
| 1059 | **43II**.2a | `vn_counterexamples_2_sup` | [S] `⋁_N ∑_{n≤N}\|n⟩⟨n\| = 1` in `B(ℓ²)` |
| 1069 | **43II**.2b | `vn_counterexamples_2_tendsto` | [S] |
| 1144 | **43II**.4a | `vn_counterexamples_4_ket` | [S] |
| 1151 | **43II**.4b | `vn_counterexamples_4_bra` | [S] |
| 1158 | **43II**.4c | `vn_counterexamples_4_star` | [B] on 4a/4b |
| 1166 | **43II**.5 | `vn_counterexamples_5` | [B] on 4a/4b |
| 1174 | **43II**.6 | `vn_counterexamples_6` | [S] |
| 1183 | **43II**.6c | `vn_counterexamples_6_sq` | [B] on 6 |
| 1192 | **43II**.11 | `vn_counterexamples_11` | [S] but the hardest of the nine (unbounded functional + Riesz on finite-dimensional subspaces) |
| 2589 | **45I**.1 | `us_cont_normal` | [S] |
| 2598 | **45I**.2 | `normal_not_us_cont` | [S] the transpose on `B(ℓ²)` |
| 2901 | **47IV**.3 | `vn_products_ncpsu` | [S] categorical; 47IV.1/.2 are proved |
| 3584 | **48III** | `gns_normal` | [L] the GNS construction (cstar.tex 30VI) is not formalized |
| 4248 | **49IV**.2 | `mn_vna_2` | [S] |
| 4308 | **49IV**.3 | `mn_vna_3` | [S] |
| 4334 | **51VII**.1 | `vna_of_faithful_countably_normal_1` | [S] |
| 4344 | **51VII**.2 | `vna_of_faithful_countably_normal_2` | [B] on 51VII.1 |
| 4365 | **51IX** | `Linfty_vn` | [L] no `L^∞` carrier in Mathlib (FIXME) |
| 4531 | **53II**.1 | `ngelfand_vna` | [S] |
| 4539 | **53II**.2 | `ngelfand_normal` | [S] |
| 4546 | **53III** | `vn_spectrum_extremally_disconnected` | [B] on 53II |
| 4680 | **54XI**.1 | `cvn_faithful_1` | [L] measure on the almost-clopen σ-algebra; large |
| 4696 | **54XI**.2 | `cvn_faithful_2` | [B] on 54XI.1 |
| 4711 | **54XI**.3 | `cvn_faithful_3` | [B] on 54XI.1 |

### The nine 43II counterexamples are now much cheaper than they look

All of them are estimates of `‖·‖_ω` and `ω(·)` for an **arbitrary**
np-functional `ω` on `B(ℓ²)`, which used to mean fighting the definition.
Since **39IX** `bh_np` (`A/CStar/TowardsVN.lean`) is proved, every such `ω`
is `∑ₙ ⟪xₙ, (·) xₙ⟫` with `∑ₙ‖xₙ‖² = ω 1 < ∞`, so

* `‖T‖²_ω = ω(T*T) = ∑ₙ ‖T xₙ‖²`, and
* each of parts 2, 4 and 6 becomes a dominated-convergence argument over `n`
  with the summable dominating family `(‖xₙ‖²)ₙ`.

`omegaNorm_vectorNP` (`Completeness.lean:757`) and `usTendsto_iff` are the
other two pieces.  This block (9 of the 24) is the cheapest volume left in
`A/VN`.

---

## What `A/Proc` needs from here

`111VII`'s condition `tensor-2` (proc.tex:2528) needs, besides 89IX:

> the family `(n,m) ↦ xₙ ⊗ yₘ` is square-summable and defines an
> np-functional on `B(ℋ ⊗ 𝒦)`, restricted to `𝒯` along the inclusion.

All four ingredients now exist:

1. **89IX** `normal_functional` (session 49) for the `xₙ` and `yₘ`;
2. **`exists_sumVectorNP`** (`NormalFunctionals.lean`, session 50) — the
   np-functional attached to a square-summable family indexed by *any* type,
   in particular `ℕ × ℕ`;
3. `sq_summable_tensor`-style square-summability of `(x,y) ↦ f(x)g(y)`,
   already in `A/Proc/Tensor.lean:192`;
4. `VNSub.restrictNP` (`A/Proc/Tensor.lean:1107`) to restrict from
   `B(ℋ ⊗ 𝒦)` to `𝒯`.

So `tensor-2` is **genuinely satisfied** as far as `A/VN` is concerned; what
remains for it is `A/Proc`-local assembly (the identity
`⟪x ⊗ y, (A ⊗ B)(x ⊗ y)⟫ = ⟪x,Ax⟫⟪y,By⟫` and a `tsum` over `ℕ × ℕ`), not a
missing theorem.  Note that `special_tensor` also carries conditions
`tensor-1` and `tensor-3`, which were never blocked on `A/VN`.
