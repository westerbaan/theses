# Semantics and logic over the two theses — four probes

Sources read: `proc.tex` 120–124 (model of the quantum lambda calculus, first and
second adjunction), 125 (`F_ha` concrete), 127 (duplicators), 132 (monoids);
`vn.tex` 42; `eff.tex` 180, 197, 199, 206, 211
(effectus, quotients, comprehension, ⋄-, &-effectus). Standing conventions: `vN`
has ncpsu maps in the Heisenberg direction; `vNᵒᵖ` is the effectus. Independent
of the other notes in this directory.

Probe (i) answers the thesis's own 120II: "we don't know whether it's possible
to interpret `let rec` in our model."

---

## (i) Recursion: `vNᵒᵖ` is dcpo-enriched, but the function type is not

**Statement A (enrichment, known).** For von Neumann algebras `A, B`, the set
`ncpsu(A,B)` with the pointwise order (`f ≤ g` iff `g−f` positive) is a pointed
dcpo: the zero map is least, and a directed family has the pointwise supremum
`(⋁f_α)(a) = ⋁_α f_α(a)` (exists by Kadison's axiom 42I(i), since `f_α(a) ≤ ‖a‖`).
The supremum is again ncpsu, and composition is Scott-continuous in both
arguments. So `vNᵒᵖ` is `DCPO⊥`-enriched, and a guarded loop
`while p do f` has the least-fixpoint semantics `⋁_n Φⁿ(0)` with
`Φ(g) = [p ⊳ g∘f ; p^⊥ ⊳ id]`.

*Where normality enters.* `g∘(⋁f_α) = ⋁(g∘f_α)` needs `g` normal — literally
42I(ii)'s definition, so the enrichment follows from Kadison's axioms with no
spatial argument; `⋁f_α` is normal by interchanging directed sups and cp by
ultraweak closedness of the cone of `M_n(B)`. Matches Ying's `while` (Löwner
chain, predual picture); known: Rennela (MFPS 2014), Cho (MSCS 2016).

**Statement B (the obstruction — believed new, checkable).** Let
`P = ncpsu(B,A)` (the closed points of type `A ⊸ B`, by 120I: `nsp(F(B)^{*A}) ≅
ncpsu(B,A)` via `Hom_miu(F(B)^{*A}, ℂ) ≅ Hom_miu(F(B), A⊗ℂ) ≅ Hom_cpsu(B,A)`).
The map `δ : P → States(F(B)^{*A})`, `f ↦ δ_f` (the nmiu functional classifying
`f`) is **neither monotone nor weak\*-continuous** for the vN-algebra order and
topology on states of `F(B)^{*A}`, whenever `P` has more than one point.

*Proof sketch.* Monotonicity: `δ_f ≤ δ_g` for two nmiu functionals forces
`(δ_g − δ_f)(1) = 0`, hence `δ_f = δ_g`; the nmiu order is discrete (this is why
`W_miu` hom-sets are discretely ordered while `W_cpsu`'s are not). Continuity:
take `A = ℂ`, `B` hereditarily atomic; by 125aIII the free algebra is concrete,
`F_ha(B) = ⊕_{r∈R_B} M_{N_r}`, one direct summand per (equivalence class of)
ncpsu map out of `B`; a state `ω : B → ℂ` corresponds to the summand `r = ω`
(`N_r = 1`), and `δ_ω` is the projection onto it. Let `e_ω` be the central
projection of that summand. If `ω_n ↑ ω` in `P` with `ω_n ≠ ω`, then
`δ_{ω_n}(e_ω) = 0` for all `n` while `δ_ω(e_ω) = 1`. (Outside the ha-restriction
the same happens with `F(ℂ) = C[0,1]^{**}`: the point atoms of the bidual
separate `δ_t` from every `δ_{t_n}`, `t_n → t`.)

*Consequence.* The thesis's model is a Moggi/Selinger–Valiron model: an LNL
adjunction `Set ⇄ W_miuᵒᵖ` plus the commutative strong monad `T = FU` whose
Kleisli category is `W_cpsuᵒᵖ` (124V), with `⟦A ⊸ B⟧ = [A, TB] = F(B)^{*A}` a
*Kleisli* exponential. The order needed for `letrec` lives in the Kleisli
category (Statement A), but the function type is an object of `W_miuᵒᵖ`, where
that order is invisible. Concretely: `⟦letrec f x = M⟧` in classical context
`ℓ^∞(G)` is a family `γ ↦ δ_{fix Φ_γ}` with `Φ_γ(f) = (ev_{γ,f} ⊗ id)∘⟦M⟧ : P → P`
(unfold `⟦!Γ⟧ ⊗ ⟦!(A⊸B)⟧ ⊗ ⟦A⟧ ≅ ∏_{G×P} ⟦A⟧`). One can *define* it by the Kleene
chain of `Φ_γ` and the unfolding rule is sound (`fix Φ = Φ(fix Φ)` plus the
substitution lemma for values). What fails is the standard *adequacy* argument
`⟦letrec⟧ = ⋁_n ⟦unfoldⁿ⟧`: the iterates' denotations `δ_{Φ_γⁿ(0)}` do not
converge to `δ_{fix Φ_γ}` in any topology `F(B)^{*A}` carries. So:

> **Answer to 120II.** `let rec` *can* be interpreted (Kleene fixpoint in `P`,
> then `δ`), and the resulting semantics is sound for the unfolding rule; but
> the model is not an `ω`-cpo-enriched LNL model in the sense needed by
> Lindenhovius–Mislove–Zamdzhiev (LNL-FPC) or Pagani–Selinger–Valiron, because
> `!`-values of function type are Dirac points of a *discrete* algebra. Adequacy
> would need an extensional order on `States(F(B)^{*A})` transported along
> evaluation, i.e. a logical relation, not the vN order.

*What would refute B.* Only a proof that the model uses `δ` solely through
`ev` — the logical-relation route, a weaker theorem ("adequate at ground
types") and the one worth proving. Note `Φ_γ` is Scott-continuous for every
*definable* `M` (induction on syntax; read the λ-case after `ev`) but not for
an arbitrary ncpsu `⟦M⟧`, since `ℓ^∞(P) ⊗ ⟦A⟧ ≅ ∏_P ⟦A⟧` admits any family:
recursion here is a syntactic, not a categorical, fixpoint.

## (ii) Hoare logic: effect-valued `wp` is Ying's; sharp `□` is not continuous

**Statement.** In the effectus `vNᵒᵖ` the substitution `f^*(q) = q∘f`
(Heisenberg `f : 𝒜 → ℬ`, `q ∈ [0,1]_ℬ`… read `f^*(q) = f(q)`) *is* the weakest
precondition of D'Hondt–Panangaden/Ying for total correctness:
`⊨_tot {p} f {q} ⟺ p ≤ f(q)`, and partial correctness is its De Morgan dual,
`wlp_f(q) = f(q^⊥)^⊥ = f(q) ⊕ (1∘f)^⊥`. Both are effect-module maps
(preserve `⊕`, `0`, scalars) and Scott-continuous (normality again). So the
*unsharp* effect logic of an effectus is exactly Ying's logic, and Ying's
relative completeness for `while`-programs transfers verbatim: the
loop rule is `wp(while) = ⋁_n wp_n`, which exists by (i).

The thesis's `f^◇(s) = ⌈f(s)⌉`, `f^□(s) = ⌊f(s)⌋` (eff.tex 206II) are the
*sharp* transformers — the Birkhoff–von Neumann projective Hoare logic:
`{p} f {s}` with `p, s` projections means "if `p` holds with certainty then
`s` holds with certainty after `f`", i.e. `p ≤ f^□(s)`. eff.tex 207III already
proves the Galois connections `f_◇ ⊣ f^□` and `f^◇ ⊣ f_□`, so the sharp logic
is a dynamic logic with `◇`/`□` in the modal sense. Its defect for programs:

**Claim.** `⌈·⌉ : [0,1]_𝒜 → Proj(𝒜)` is Scott-continuous (`⌈⋁a_n⌉ = ⋁⌈a_n⌉`,
since `ker(⋁a_n) = ⋂ ker(a_n)`), but `⌊·⌋` is not: `a_n = (1−1/n)·1` has
`⌊a_n⌋ = 0`, `⌊⋁a_n⌋ = 1`. Hence `while^□` computed as `⋁_n while_n^□` is
strictly weaker than `⌊wp(while)⌋`: the sharp `□`-logic is sound but incomplete
for loops that terminate with probability one but not with certainty. `◇`
(strongest sharp postcondition, "reachability") has no such defect — the
asymmetry is the same as ∃ vs ∀ under ω-chains.

*What would refute it.* A proof that `⌊·⌋` commutes with the suprema that
actually arise as loop iterates — false already for `while (coin) skip`.

*Internal logic (Jacobs's effect logic).* Predicates form the fibration
`∫Pred → C` of effect modules; the structural rules are substitution `f^*`,
`⊕` with side condition `p ⊥ q`, `⊥`-negation, scalars; in an `&`-effectus
also `p & q := q∘asrt_p` (non-commutative conjunction; `p & q = p ∧ q` iff
compatible). Quantifiers: `∃_f = f_◇` and `∀_f = f^□` exist only on *sharp*
predicates; on effects, `f^*` has no right adjoint (`max{q : ω(q) ≤ λ}` for a
state `ω` does not exist), so the unsharp logic is quantifier-free. A sequent
calculus should therefore be a two-layer system: an effect-module layer (sound,
complete for `vNᵒᵖ` by Ying) and a modal projective layer on top of it, related
by `⌈·⌉ ⊣ inclusion ⊣ ⌊·⌋`.

---

## (iii) Linear logic: affine ILL with an idempotent Lafont `!`, not `*`-autonomous

**Correction first.** Duplicators exist not for commutative algebras but for
`ℓ^∞(X)` only (127III): `L^∞[0,1]` has no comultiplication because the diagonal
of `[0,1]²` is null. So the `!`-coalgebras are *discrete* classical types, and
"continuous classical data" is not duplicable in this model.

**Statement.** `W_miuᵒᵖ` with `⊗`, unit `ℂ`, internal hom `[A,B] = B^{*A}`
(Kornell, 124–125) is a symmetric monoidal closed category and:

1. *Affine.* `ℂ` is initial in `W_miu`, so the unit is terminal in `W_miuᵒᵖ`:
   weakening holds for all types (as in Selinger–Valiron's QLC).
2. *Additives.* `⊕` = direct sum (vn.tex 42V); `&` = free product of von Neumann
   algebras (coproduct in `W_miu`, exists by AFT); `⊗` distributes over `⊕`
   since `B ⊗ −` preserves products (124IV's proof).
3. *Lafont exponential.* `!A = ℓ^∞(nsp A)` is the free commutative `⊗`-comonoid
   (132IV); `ℓ^∞ ⊣ nsp` is a monoidal adjunction (123I, 123II both strong
   monoidal), so `Set ⇄ W_miuᵒᵖ` is a Benton LNL model.
4. *Idempotent.* `nsp(ℓ^∞ X) ≅ X` (122VI) gives `!!A ≅ !A`; `ℓ^∞` is fully
   faithful, so the adjunction is comonadic and `!`-coalgebras `≃ Set`. The
   model identifies `!A` with the largest `ℓ^∞`-summand of `A`;
   `!M_2 = ℓ^∞(∅) = {0}` = the initial object of `W_miuᵒᵖ`, i.e. `!qbit = 0`.
5. *Not `*`-autonomous, for any dualizing object.* If `D` dualizes then
   `[[ℂ,D],D] ≅ ℂ`, i.e. `D^{*D} ≅ ℂ`, i.e. `Hom_miu(D, D ⊗ Y)` is a singleton
   for every `Y`; with `Y = D` the maps `d ↦ d⊗1` and `d ↦ 1⊗d` differ unless
   `D = ℂ`. But `[A,ℂ] = ℂ^{*A} = ℂ` for all `A` (`Hom_miu(ℂ, A⊗Y)` is a
   singleton), so `[[A,ℂ],ℂ] = ℂ ≠ A`. No `⅋`, no involutive negation, no
   classical cut.

So the model validates exactly intuitionistic affine MELL+additives with a
free exponential; the "quantum" content is entirely in the Kleisli monad
`T = FU` (measurement, mixing), which is commutative: strength
`A ⊗ TB → T(A⊗B)` is `id ⊗ u_B` under the adjunction, and both composites
`TA ⊗ TB → T(A ⊗ B)` are `u_A ⊗ u_B`. This is precisely Selinger–Valiron's
"linear category for duplication + strong monad with `T`-exponentials"
(and Egger–Møgelberg–Simpson's enriched effect calculus with a trivially
enriched value category).

*What would refute it.* A non-`ℓ^∞` commutative comonoid in `W_miuᵒᵖ` (ruled
out by 127III), or a second nmiu map `ℂ → A⊗Y` (ruled out by unitality). Item
5 says nothing about a weak `⅋`/linear distributivity; I see no candidate.

---

## (iv) Dependent types: a comprehension category with `Σ`, without `Π`

**Statement.** For a ⋄-effectus, `∫Pred → C` with the four-adjunction chain
`Q ⊣ 0 ⊣ π ⊣ 1 ⊣ K` (eff.tex 197IV, Cho–Jacobs–Westerbaan²) is a comprehension
category with unit in Jacobs's sense (`1 ⊣ K = {−}`) *and* its dual
(`Q ⊣ 0`). The dependent type theory it models has: subset types
`{x : X | p}` with `Σ_{x:X} p := {X|p}` (weak Σ along the display map
`π_p : {X|p} → X`, since `π_p^*` has left adjoint `(π_p)_◇` on sharp
predicates); quotient types `X/p` as *co*-subset types — the same object as
`{X|p^⊥}` when `p` is sharp in `vNᵒᵖ`, with the map in the other direction
(`asrt`, the filter), so the theory is one of *retracts* `X/p ⇄ X ⇄ {X|p}`,
which in a `†`-effectus become a dagger pair. `Π` fails: `f^*` on `[0,1]_A` has
no right adjoint (ii), and even on sharp predicates `∀_f = f^□` is only a
poset adjoint, not a fibred one (the sharp fibration has no cartesian
`f^*`, only `f^◇` approximating it).

*Plausibility.* High for the structure; low for the name "dependent type
theory": `Pred(X)` is indexed by objects, not terms — Jacobs's "logic over a
type theory", not Martin-Löf. *Refutation:* a ⋄-effectus where `π_p` fails to
be a display map (comprehensions are total, eff.tex 199III, so none).

---

## Verdict

Best: **(i)**, Statement B — a precise, new, checkable obstruction that
answers the thesis's own open question 120II in the nuanced form "definable but
not adequately so", localised to the discreteness of `F` (visible already in
125aIII's `F_ha = ⊕ M_{N_r}`). Second: (ii)'s `⌊·⌋`-discontinuity, small but
sharp. (iii) is a clean classification (affine ILL, idempotent Lafont, not
`*`-autonomous, duplicators = discrete only) that corrects the brief's
premise. (iv) is structure-collecting, not a theorem. Next step for (i):
adequacy at ground types via `R_{A⊸B}(ρ) := ∀a. ev∘(ρ⊗a) ∈ R_B`, in the
ha-restriction (125a) where `F_ha` is explicit.
