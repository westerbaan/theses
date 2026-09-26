# Can `JBWExceptionalSummand` be proved in-repo? (H-O–S 7.2.7 route) — research note

Status: **claimed**, not reviewed. No Lean written. 2026-09-26.

## Target

`JBWExceptionalSummand` (Rec136Hyps.lean:62): every JBW `V` is `IsJWAlgebra` (Algebras.lean:324:
injective **normal** Jordan hom into a Kadison vN algebra) **or** has a central idempotent
`c ≠ 0` with `ψ(cV) = 0` for **every** Jordan hom `ψ` into **every** C*-algebra (universe `v`).

Downstream use (`rec135_native`, `native_absurd`): the JW branch must give `IsJWAlgebra`
(it is the `jw` field of `JWnpcCat`, the goal of REC 135/136, so normality is essential);
the other branch feeds `corner_of_summand` → object `W` with `V_W` **purely exceptional**,
which is consumed by `ExceptionalAlbertMap` and by `false_of_smallSpan` (a non-zero,
generally **non-normal** Jordan hom `V_W → C(Fin n, ℂ)` built from Shultz's point
evaluation). So "killed by every Jordan hom, normal or not" is genuinely used.

## The route, step by step

Let `J = ⋂ {ker ψ : ψ Jordan hom V → 𝔅, 𝔅 C*}` ("special kernel") and
`J_n = ⋂ {ker φ : φ normal Jordan hom V → 𝔄, 𝔄 vN}`.

**(A) `J_n = cV`, `c` central, and `(1-c)V` JW — provable with current infrastructure.**
1. Small index set: for each `x ∉ J_n` choose a witness `(𝔄_x, φ_x)`; index by `x : V`
   (stays in universe `v` — needs the witness vN algebras in universe `v`, which
   `IsJWAlgebra`/the Prop already fix).
2. Product: tree `Theses/A/VN/Basic.lean:1053` gives `VonNeumannAlgebra (lp 𝒜 ∞)`, with
   `vn_products_proj_normal` / `vn_products_nmiu` (normal maps into a product ⇔ normal
   coordinates). `Φ = (φ_x)_x : V → lp 𝒜 ∞` is a normal Jordan hom with `ker Φ = J_n`.
   Needs: bounded family (Jordan homs into C* are contractive — ‖φ a‖ ≤ ‖a‖ via
   `JBCalculus` C(a) ≅ C(sp a) and the positive-unital case; ~150 lines), Jordan identity
   and self-adjointness coordinatewise (trivial).
3. `ker Φ` is a norm-closed Jordan ideal closed under directed sups of its positive part
   (normality + `U_a`-invariance). A monotone-closed Jordan ideal `I` of a JBW-algebra is
   `cV`: for `a ∈ I₊` the range projection `r(a)` (`JBWProj` spectral/range projections,
   `sproj_isLUB`) is a monotone limit of `f_n(a) ∈ I` (`f_n(0)=0`, norm-closed ideal) so
   `r(a) ∈ I`; `c = sup` of these (`exists_sSup_idem`, JBWProj:1502) lies in `I`, is fixed by
   every Peirce reflection because `I` is (`U_s I ⊆ I`), hence central (`central_of_Ph`,
   JBWProj:1386, same pattern as `exists_central_cover`); `I = cV` since `x = cx` for
   `x ∈ I` (spectral decomposition; `JBPeirce`) and `cV ⊆ I` by ideal. ~400 lines.
4. `(1-c)V` is JW: restrict `Φ` (injective on `(1-c)V`, normal). Transport to a
   `JBWAlgebra` structure on the corner (`CentralIdem` corners, `JBWSEA.lean`). ~200 lines.
   Total (A): **~800–1,100 lines**, all ingredients present.

**(B) `cV` is purely exceptional (i.e. `J = J_n`) — the crux; NOT available.**
Need: every (non-normal) Jordan hom `θ : V → 𝔅` kills `cV`. Equivalently `J` is
monotone (weak*) closed. The obvious reduction fails:
- "Normalise" `θ`: `N₊ = {f ∈ 𝔅*₊ : f∘θ normal}` is `Ad`-invariant (for monomials
  `x = θ(v₁)…θ(v_k)`, `x* θ(·) x = θ∘U_{v_k}…U_{v_1}`; general `x` by
  `(a+b)*D(a+b) ≤ 2a*Da + 2b*Db` and norm density), and `⊕_{f∈N₊} π_f ∘ θ` is a normal
  Jordan hom (vector-state argument as in FDS/Bidual.lean). **But** its kernel is only
  `⊇ ker θ`; if `ker θ ⊇ J` is weak*-dense in `cV`, every normal state vanishing on
  `ker θ` vanishes on `cV`, so the normalisation is `0` on `cV` — no contradiction. The
  non-normal part of `θ` is exactly what (B) must control (cf. the Calkin-type
  situation: norm-closed weak*-dense ideals exist, e.g. `K(H) ⊂ B(H)`).
- In H-O–S the proof of 7.2.7's "`cM` purely exceptional" goes through the structure
  theory, not through `W*(M)`: type I_n (n≠3) and types II/III parts are JW (spin factors;
  coordinatisation from ≥4 / ≥3 exchangeable projections, H-O–S 5.3, 6.x, 7.2.x — the
  REC 132 content), and the remaining type I₃ exceptional part is `C(X, H₃(𝕆))`,
  killed by all Jordan homs into C*-algebras via Glennie's identity (H-O–S 7.2.x /
  2.4.x). So (B) ≈ REC 132 (coordinatisation, est. >3,000 lines in Rec136Hyps header)
  + Glennie's identity in `M₃(𝕆)_sa` + type decomposition. Estimate **4,000–6,000 lines**;
  not recommended now.

## Weaker variants for REC 136

1. **"JC or summand" instead of "JW or summand"** — does not help: the summand branch is
   the same crux (B). The JW branch could be recovered from JC by the normalisation above
   (claimed lemma **JC⇒JW**: a JBW-algebra with an *injective* Jordan hom `θ` into a
   C*-algebra is JW; proof: injective Jordan homs are order embeddings (JBCalculus), so
   every normal state `ω` extends (M. Riesz/Krein, `θ(V)` contains the unit) to `f ∈ N₊`
   with `f∘θ = ω`; separating normal states ⇒ normalised hom injective. ~700 lines, needs
   GNS direct sums as in Bidual.lean.) Useful only if some future Prop hands out JC.
2. **"JW or normal-summand"** (`c ≠ 0`, every *normal* Jordan hom into a vN algebra kills
   `cV`): fully provable by (A) (~1,000 lines). But then `native_absurd` breaks:
   `ExceptionalAlbertMap` needs `IsPurelyExceptional`, and `false_of_smallSpan` produces a
   non-normal hom into `C(Fin n, ℂ)`. One would have to strengthen the named REC 55 Prop to
   "normally-exceptional ⇒ Albert map", which is REC 55 **plus** (B) — just moving the crux
   into a named hypothesis (and a statement change: needs the author, cf. alignment ruling).
3. **REC-supplied data**: nothing in REC's structure (states, `⊗`, comprehension) seems to
   yield normality of arbitrary Jordan homs or density-closedness of `J`; the tensor trick
   of `Rec136Native` works *inside* an already exceptional corner. No shortcut found.

## Minimal missing lemma

`special_kernel_weakstar_closed`: for a JBW-algebra `V`, if `c` is the central idempotent
with `J_n = cV` (from (A)), every Jordan hom of `V` into a C*-algebra vanishes on `cV`.
Everything else in `JBWExceptionalSummand` reduces to (A) with present infrastructure.

## Recommendation

- Do **not** attempt a full proof now. If desired, prove (A) as a standalone file
  (`Papers/REC/JBWNormalSummand.lean`, ~1,000 lines) and restate
  `JBWExceptionalSummand` as (A) + the single named Prop `special_kernel_weakstar_closed`
  (strictly weaker hypothesis; equivalent content to "J is weak*-closed"). This isolates
  the literature dependency to one clean analytic statement (H-O–S 7.2.x / structure
  theory), but it is bookkeeping, not an elimination.
- Before building: adversarial review of step (A)3 (ideal ⇒ `cV`: check `x = c x` for all
  `x ∈ I`, not only positive; and `U_s`-invariance of monotone-closed Jordan ideals) and of
  the universe handling in (A)1–2.

## Review (2026-09-26)

Adversarial spot-check; no Lean. Verdict: (A) STANDS with two small gaps; (B) correctly
identified as the crux; universe handling STANDS.

* (A)1–2 universes: `IsJWAlgebra` fixes the vN algebra in `V`'s universe, so each witness
  `𝔄_x : Type v`, index `x : V : Type v`, product `lp 𝔄 ∞ : Type v`. Correct. The uniform
  bound needs contractivity of (non-unital) normal Jordan homs: `φ 1` is a projection and
  `φ` is positive, so `‖φ a‖ ≤ ‖a‖`; fine, but the ~150-line estimate should include the
  non-unital case.
* (A)3 gap 1: `c = sup {r(a) : a ∈ I₊}` lies in `I` by monotone closure only if the family
  is **directed**. Needs `r(a), r(b) ≤ r(a+b)` for `a, b ≥ 0` (from `a ≤ a+b` and
  "`x ≤ y`, `y ∈ U_e V` ⇒ `x ∈ U_e V`"); not listed. Alternatively close `I` under sups of
  finite families of idempotents first. ~50 lines.
* (A)3 gap 2 (the reviewer question "`x = cx` for all `x ∈ I`"): clean argument —
  `y := x − cx ∈ I` (ideal, `c ∈ I`), `y ∈ (1−c)V`, so `r(y²) ≤ c` and `r(y²) ≤ 1−c`,
  hence `r(y²) = 0`, `y² = 0`, `y = 0`. Uses `r(y²) ≤ c` for `y² ∈ I₊` (definition of `c`)
  and `y² = 0 ⇒ y = 0` (JB norm). No spectral decomposition needed.
* `U_s I ⊆ I` is immediate for any Jordan ideal (`U_s x = 2s(sx) − s²x`), and `U_s` is an
  order automorphism for a symmetry, so `U_s c = sup r(U_s a) ≤ c`; with `s² = 1` equality.
  `central_of_Ph` then applies (via Peirce reflections `2e−1`). Correct.
* (A)4: `CentralIdem.Corner` already has `JBWAlgebra` (JBWSEA.lean:424). Restriction of `Φ`
  to `(1−c)V` is injective (`ker Φ ∩ (1−c)V = cV ∩ (1−c)V = 0`) and normal. Correct.
* (B): agreed it is not available, and that normalisation loses exactly the non-normal part
  (Calkin analogy apt). `special_kernel_weakstar_closed` is true (by 7.2.7) and together with
  (A) gives `JBWExceptionalSummand` (case `c = 0`: JW; `c ≠ 0`: the summand). Correct.
* JC⇒JW side claim: the Ad-invariance argument only covers `x ∈ C*(θ(V))`; restrict `f` to
  `C*(θ(V))` before GNS (cyclic vectors then come from monomials). With that, plausible.
