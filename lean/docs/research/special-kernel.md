# `SpecialKernelNormal` is not needed: REC 136 from the normal kernel alone — research note

Status: **claimed**, not reviewed, no Lean written, nothing compiled. 2026-09-26.
Scope: (a) REC 136 with only the *normal* half (`J_n = cV`, proved in `JBWSummandA.lean`);
(b) `SpecialKernelNormal` in general; (c) the obstruction to (b).

## 0. Answer

**(a) Yes — and the result is that REC 136 becomes UNCONDITIONAL** (no `JBWExceptionalSummand`,
no `SpecialKernelNormal`, no Shultz, no H-O–S 7.2.7). With `Papers/REC/JBCoord.lean`
(`rec136_summand_hypfree`: REC 136 from `JBWExceptionalSummand` alone), the *only* place a
Jordan homomorphism into a C*-algebra is fed to pure exceptionality is
`corner_absurd` (JBCoord:474, `hpe (Hs β →L[ℂ] Hs β) Φ hΦJ`) plus one hidden use,
`pe_exists_exch_pair` → `centralIdem_not_assoc` (JBWProj:1632, Gelfand into `C(X, ℂ)`, not a
vN algebra, not normal). Both can be made **normal Jordan homs into von Neumann algebras**:

1. `corner_absurd`: choose the state `φ` **normal** (`V = V_{W⊗W}` is JBW: separating normal
   states, `Q ≥ 0`, `Q ≠ 0` ⇒ some normal `φ` has `φ Q > 0`). Then `Φ : a ↦ opC(2ψ(a)·)` into
   `B(Hs)` — a von Neumann algebra (`Theses/A/VN/Basic.lean:764`, Kadison, Loewner order
   `ContinuousLinearMap.instLoewnerPartialOrder`) — is normal (§1). Hence
   `IsNormallyPurelyExceptional U` (every normal Jordan hom into a vN algebra of universe `v`
   vanishes) suffices, and for `U = V_W ≅ cV_A`, `cV_A = J_n` gives exactly that **by
   definition of `J_n`** (`normalKernel_eq_corner`).
2. Associative case: replace Gelfand by the **GNS construction for an associative JBW-algebra**
   with the same `PsdForm/Cx/Hs/opC` machinery of JBCoord §2 (§2 below); its vector
   functionals are `c ↦ φ(U_x c)`, normal by the same lemma. No `C(X, ℂ)` vN structure needed.

**(b)/(c)**: no structure-free proof found; the precise content: `SpecialKernelNormal ⟺`
(for every JBW `V`: `IsNormallyPurelyExceptional V → IsPurelyExceptional V`) (§4). With (a)
it is no longer on REC's path; it stays only as the bridge from H-O–S/Shultz statements.

## 1. Normality of `Φ = opC ∘ T` (the core claim)

Setting of `corner_absurd`: `V` JBW, `P ⊥ Q` idempotents, `w` connecting, `ψ : U → V` Jordan,
`ψ 1 = P`, `W = V½(P) ∩ V½(Q)`, `β(x, y) = φ(Q(xy))`, `T_a = 2L_{ψ(a)}` on `W`, `Hs = ` completion
of `Cx β = W × W`, `Φ a = opC β (T_a)`.

**Vector functionals.** For `u = (x₁, x₂) ∈ Cx β`, `⟪Φ(a)u, u⟫ = β(T_a x₁, x₁) + β(T_a x₂, x₂)`
(the imaginary part vanishes because `T_a` is `β`-symmetric, `Lc_symm`), and
`β(T_c x, x) = 2φ(Q((cx)x)) = φ(U_Q U_x c)` for `Qc = 0` (`jQ_jQ_eq`, JBCoord:103; `ψ(a) ∈ V₁(P)
⊆ V₀(Q)`, `Q_mul_of_one`). So `ρ_u := ⟪Φ(·)u, u⟫ = ω_u ∘ ψ` with
`ω_u := φ ∘ U_Q ∘ U_{x₁} + φ ∘ U_Q ∘ U_{x₂}`, a **positive** functional on `V` (`JBMac.jQ_nonneg`).

**Lemma N1 (claimed) `isNormal_jQ`.** `V` JBW, `ω` positive normal functional, `r : V` ⇒
`ω ∘ U_r` is normal. Proof: with `t = ‖r‖`, `a := r + t·1 ≥ 0`, `b := t·1`: the polarisation
identity `U_{a−b} c + U_{a+b} c = 2U_a c + 2U_b c` (quadratic in `a`, pure `module`) and
`U_{a+b} c ≥ 0` for `c ≥ 0` give `ω(U_r c) ≤ 2ω(U_a c) + 2t² ω(c)`. `U_a = ‖a‖² U_{a/‖a‖}` and
`JBAllSEA.jQ_isLUB` (`0 ≤ r' ≤ 1`, LUBs in `[0,1]`; general directed `S` with LUB `s` by
passing to the cofinal `{a ≥ a₀}`, translating by `a₀`, scaling by `‖s − a₀‖`) make
`ω ∘ U_{a/‖a‖}` normal. Finish by **domination**: a positive functional `≤ K·ω'` on `V₊` with
`ω'` positive normal is normal (the proof of `isNormal_of_dom`, JBWProj:371, verbatim:
`ψ(s) − ψ(d) ≤ K ω'(s − d)`). ~100 lines. (`isNormal_P1` covers `U_Q, U_P` directly.)

**Lemma N2.** normal positive functional `∘` monotone normal map is normal (image of a
directed set is directed; 15 lines). Sums and positive scalings of normal positive functionals
are normal (`isNormalMap_smul` exists).

**Lemma N3 (claimed) `opC_normal`.** `Φ : U →ₗ B(Hs)` a Jordan hom (positive by
`jordanHom_nonneg`, JBWSEA:164) with `ρ_u` normal for every `u : Cx β` ⇒ `IsNormalMap Φ`.
Proof: `S` directed, `IsLUB S s`. Upper bound: monotone. Least: `B ≥ Φ a` for all `a ∈ S`.
`R := B − Φ s` is self-adjoint (`B − Φ a₀ ≥ 0` and `Φ` self-adjoint valued). For `u ∈ Cx β`:
`re⟪Bu,u⟫ ≥ ρ_u(a)` for all `a` (`nonneg_iff_isPositive`, `isPositive_iff_complex`), and `ρ_u`
normal gives `ρ_u(s) = sup ρ_u(S) ≤ re⟪Bu,u⟫`, i.e. `re⟪Ru,u⟫ ≥ 0`. `ξ ↦ re⟪Rξ,ξ⟫` is
continuous and `Cx β` is dense (`UniformSpace.Completion.induction_on`, `isClosed_le`, as in
`opC_selfAdjoint`), so `R ≥ 0` by `isPositive_iff_complex` ⇒ `Φ s ≤ B`. ~120 lines.
(A dense *subspace* suffices — positivity is tested on all `ξ`; a total set would not.)

**Assembling.** `ρ_u = ω_u ∘ ψ`; `ω_u` normal by N1 (twice) + sums; then the hypothesis on `ψ`:
`hψN : ∀ ω positive normal on V, ω ∘ ψ normal on U`. In the REC glue `ψ a = P·(a ⊗ 1)` and
`P·z = U_P z` on the image (`hPP`: `P(Pz) = Pz` ⇒ `U_P z = 2P(Pz) − Pz = Pz`), so
`ω ∘ ψ = (ω ∘ U_P) ∘ ι` with `ω ∘ U_P` normal (N1 or `isNormal_P1` via `P1_eq_jQ`) and
`ι = (· ⊗ 1)` monotone normal (`rec127`, parts 3–4) — N2. Hence `Φ` is a **normal** Jordan
hom `U → B(Hs)`, non-zero at `1` exactly as in `corner_absurd`.

## 2. The associative case without `C(X, ℂ)`: GNS

`npe_exists_exch_pair (hpe : IsNormallyPurelyExceptional V) (h1 : 1 ≠ 0)`: `exists_exch_pair`
unless `V` associative; if associative (`hB`): `φ` any normal state (exists: separating normal
states, `1 ≠ 0`); `PsdForm` on `W := V`, `β(x,y) := φ(xy)` (symmetric, `φ(x²) ≥ 0`);
`T_a := L_a`. `IsBdd`: `φ((ax)²) = φ(a²x²) ≤ ‖a‖² φ(x²)` since `(‖a‖²·1 − a²)x² ≥ 0`
(product of positives in an associative JB-algebra: `nonneg_iff_gelfand` + `gelfand_mul`);
`β`-symmetric and `L_{ab} = L_a L_b` by associativity+commutativity, so `a ↦ opC β (L_a)` is a
Jordan hom into `B(Hs)`, `= 1 ≠ 0` at `1` (`one_ne_zero_of_pos`, `β(1,1) = 1`). Vector
functionals `c ↦ φ((cx)x) = φ(x² c) = φ(U_x c)` (associative: `U_x = L_{x²}`): normal by N1;
N3 ⇒ normal. Contradiction with `hpe`. ~130 lines; reuses JBCoord §2 unchanged.

## 3. Exact Lean changes (new file, e.g. `Papers/REC/JBCoordNormal.lean`; no statement edits)

* `def IsNormallyPurelyExceptional.{u,w} (A)`: `∀ (𝔄 : Type w) [CStarAlgebra 𝔄] [PartialOrder 𝔄]
  [StarOrderedRing 𝔄] [Theses.VonNeumannAlgebra 𝔄] (φ : A →ₗ[ℝ] 𝔄), IsJordanHomInto A 𝔄 φ →
  IsNormalMap φ → φ = 0`. Trivially `IsPurelyExceptional → IsNormallyPurelyExceptional`.
* `JBWNormalSummand.{v}` (proved from `JBWSummandA`): `IsJWAlgebra V ∨ ∃ c ≠ 0` central idem,
  `∀ 𝔄 vN, ∀ φ normal Jordan hom, ∀ x, c x = x → φ x = 0` — the proof of
  `jbwExceptionalSummand_of_specialKernel` with `h` replaced by `(hker x).2 hx`.
* Lemmas N1–N3 (§1), `isNormal_of_le` (domination), `exists_normal_state_pos`
  (`0 ≤ Q ≠ 0 ⇒ ∃ normal state, φ Q > 0`).
* `corner_absurd_normal`: as `corner_absurd` with `[JBWAlgebra V]`,
  `hpe : IsNormallyPurelyExceptional.{v,v} U`, extra `hψN` (§1), `φ` from
  `exists_normal_state_pos`; ends with `hpe _ Φ hΦJ (opC_normal …)`. Universe: `Hs β : Type v`.
* `assoc_absurd_normal` (§2) and `npe_exists_exch_pair`.
* `corner_of_summand_normal` (Rec136Hyps:267 variant): hypothesis `hvan` over normal Jordan
  homs into vN algebras, conclusion `IsNormallyPurelyExceptional (VA σs W)`; the proof of
  `Monoidal.corner_purelyExceptional` with `ψ ∘ₗ J` normal: `stateLin_normal σs (comprMap c)`
  (Reconstruction2:271) and `stateLin_nonneg` (monotone), N2.
* `summand_absurd_normal`: `summand_absurd` with `npe_exists_exch_pair` and
  `corner_absurd_normal`, `hψN` discharged as in §1 ("Assembling").
* `rec135_unconditional (A : C) : IsJWAlgebra (VA (realSplit ψ₀) A)`: `normalKernel_eq_corner`;
  `c = 0` ⇒ `exists_normal_hom_ker` is injective (JW); `c ≠ 0` ⇒ `corner_of_summand_normal` ⇒
  `summand_absurd_normal`. Then `rec136_unconditional` with the statement of
  `rec136_hypfree` and **no hypotheses** (`jwFunctor_spec` as in `rec136_summand`).
* Nothing else in the chain consumes `IsPurelyExceptional` (`rec136_summand` needs only
  `IsJWAlgebra` per object). Estimate ~750 lines.

## 4. (b), (c): `SpecialKernelNormal` itself

* **Reformulation (claimed).** `SpecialKernelNormal ⟺ ∀ V JBW, IsNormallyPurelyExceptional V
  → IsPurelyExceptional V`. (⇒) `J_n = V`. (⇐) `x ∈ J_n = cV`; `cV` (`CentralIdem.Corner`, JBW)
  is normally purely exceptional (normal homs of `cV` extend along the normal `proj`), hence
  purely exceptional; `ψ|_{cV}` vanishes. Also `⟺ J` (special kernel) is monotone-closed.
* **Bidual picture (why no structure-free proof).** For `ψ : V → 𝔅` a Jordan hom, `ψ**` is a
  normal hom `V** → 𝔅**` (JW), and `V** = zV** ⊕ (1−z)V**` with `zV** ≅ V` normally; normal
  pure exceptionality kills `ψ**` on `zV**`, so `ψ = ψ** ∘ (x ↦ (1−z)x)` factors through the
  **singular** embedding of `V` into `(1−z)V**`. (b) is exactly "normal pure exceptionality of
  `V` passes to the singular part `(1−z)V**`": true in the model (`C(X, Alb)** = C(X', Alb)`),
  but every proof known to me goes through H-O–S 7.2.x: `J_n = V` ⇒ type I₃ ⇒ `C(X, Alb)` ⇒
  Glennie. Identity routes (Glennie ideal `⊆ J_n` trivially; the converse is again the
  structure theorem) and normalisation of `ψ` (loses the singular part, cf. hos727 note)
  fail. Biduals of JB-algebras are not in the tree either.
* **Source alignment.** H-O–S 7.2.7's proof runs: *normally* exceptional summand ⇒ structure
  theorem ⇒ Glennie; a Prop `ShultzExceptionalStructureN` (hypothesis
  `IsNormallyPurelyExceptional`) would be the faithful form of that step and would yield
  `SpecialKernelNormal` (plus Glennie, not in the tree). Irrelevant for REC after §3.

## 5. Risks to review

* N1's reduction of arbitrary directed sets to `[0,1]` (cofinal subset, translation, scaling);
  `jQ_isLUB` is stated for any JB-algebra, `r ∈ [0,1]`.
* N3: the order of `Theses.VonNeumannAlgebra (H →L[ℂ] H)` is Mathlib's Loewner order
  (`inner_diag_mono`, `A/VN/Basic.lean:730`, uses `nonneg_iff_isPositive`/`isPositive_iff_complex`).
* `⟪Φ(a)u,u⟫` real with the stated formula: check `Cx.inn` against `Tc_re/Tc_im` and `Lc_symm`.

## Review (2026-09-26)

Adversarial review, read-only (no Lean, no compile). Sources re-read: JBCoord (corner_absurd,
summand_absurd, rec135_summand, rec136_summand{,_hypfree}), JBWSummandA (normalKernel,
normalKernel_eq_corner, exists_normal_hom_ker, jbwExceptionalSummand_of_specialKernel),
Rec136Hyps (JBWExceptionalSummand, corner_of_summand), Monoidal (corner_purelyExceptional,
rec127), Reconstruction2 (stateLin_normal), JBWProj (isNormal_of_dom, centralIdem_not_assoc,
pe_exists_exch_pair), JBAllSEA (jQ_isLUB), A/VN/Basic (B(H) instance), Algebras (defs).
Numpy (scratch revsk-1.py): β(T_c x, x) = φ(U_Q U_x c) on 4×4 Hermitian with P,Q diagonal
blocks, c ∈ V₁(P), x off-diagonal — equal to 1e-15; polarisation identity — 5e-15.

**N1 `isNormal_jQ` — STANDS.** `jQ_isLUB` needs `0 ≤ r ≤ 1`, `S ⊆ [0,1]`, `x ∈ [0,1]`, IsLUB in
the whole algebra, *no* directedness. Reduction checked: a₀ ∈ S, S' = {a ∈ S | a₀ ≤ a} has the
same upper bounds (directedness), S'' = k⁻¹(S' − a₀), k = ‖s − a₀‖ (k = 0 ⇒ S' = {s}), lies in
[0,1] with LUB k⁻¹(s − a₀) ∈ [0,1]; U_r linear + monotone for every r (`jQ_mono r`) transports
back and U_r(S) has the same upper bounds as U_r(S'). Scaling r ≥ 0 to [0,1]: U_{tr} = t²U_r.
General r: a = r + ‖r‖1 ≥ 0, U_r c ≤ 2U_a c + 2‖r‖²c for c ≥ 0 (polarisation + U_{a+b}c ≥ 0);
domination argument = `isNormal_of_dom` verbatim, but restated for a positive functional
dominated by K·ω' with ω' positive normal (not an `OUSState`) — cosmetic.

**N2 (ι = ·⊗1 normal) — STANDS.** `rec127` part 4 is literally `IsNormalMap (a ↦ a ⊗ 1)` in
the repo's sense (it is `stateLin (rhoMap A B)`, `stateLin_normal`); part 3 gives monotone.
ψ a = P·ι a = U_P ι a (from `hPP`), so ω∘ψ = (ω∘U_P)∘ι, normal. Composition lemma needs
the inner map monotone (directed image) — available.

**N3 `opC_normal` — STANDS.** Order on B(Hs) is Mathlib's Loewner order; the
`VonNeumannAlgebra (H →L[ℂ] H)` instance (A/VN/Basic:764) is for any `H : Type*`, so
`B(Hs β) : Type v` is admissible in `normalKernel`'s binder. `IsNormalMap` tests IsLUB in all
of B(H) (not selfAdjoint): an upper bound B of Φ(S) has B − Φ a positive, hence B s.a.;
R = B − Φ s s.a.; re⟪Rξ,ξ⟫ ≥ 0 on coe(Cx β) from normality of ρ_ξ; closed set + `denseRange_coe`
⇒ all of Hs; s.a. + that ⇒ IsPositive. Uniform boundedness not even needed (R is one fixed
bounded operator). Upper-bound half from `jordanHom_nonneg`.

**(4) vector-functional formula — STANDS.** `inn` re-part is β(re,re) + β(im,im), symmetric,
so re⟪Φ(a)u,u⟫ = β(T x₁,x₁) + β(T x₂,x₂); β(2cx, x) = 2φ(Q((cx)x)) = φ(U_Q U_x c) by
`jQ_jQ_eq` with Qc = 0 (`Q_mul_of_one`). Positivity of ρ_u: φ, U_Q, U_x, U_P, ι all positive.
Normal φ with φ Q > 0: separating normal states give ω(Q) ≠ ω(0) = 0, and Q ≥ 0.

**(5) associative case via GNS — STANDS, and simpler than claimed.** In an associative JB
algebra (ab)x = a(bx), so L_{ab} = L_aL_b = ½(L_aL_b + L_bL_a), β(ax,y) = β(x,ay), and
U_x c = c·x². Boundedness: (‖a‖² − a²)x² = U_x(‖a‖²1 − a²) ≥ 0 by `jQ_nonneg` — no Gelfand
(`nonneg_iff_gelfand`/`gelfand_mul`) needed. β(1,1) = φ(1) = 1. Vector functionals
c ↦ φ(U_{x₁}c) + φ(U_{x₂}c): N1. A normal state exists (separating, 1 ≠ 0).

**(6) other uses of `IsPurelyExceptional` on the path — none.** summand_absurd consumes hpe
only in `pe_exists_exch_pair` and `corner_absurd`; corner_of_summand only *produces* it (via
`Monoidal.corner_purelyExceptional`, whose proof is φ∘J with J = `stateLin (comprMap c)`:
normal by `stateLin_normal`, monotone by `stateLin_nonneg`, so the normal variant goes through
verbatim); `jwFunctor_spec` needs only per-object `IsJWAlgebra`; trivial-split branch unchanged.

**(7) sufficiency for an unconditional rec136 — STANDS.** c from `normalKernel_eq_corner`
(needs only `JBWAlgebra`, from `jbw_real`); c = 0 ⇒ `exists_normal_hom_ker` injective ⇒ JW
(exactly the c = 0 branch of `jbwExceptionalSummand_of_specialKernel`); c ≠ 0 ⇒ hvan over
normal homs from `(hker x).2`; corner ⇒ `IsNormallyPurelyExceptional (V_W)` ⇒ False. Universes
all `v`. Result: rec136_hypfree's statement with no hypotheses beyond hirr, h01.

**§4 (b)/(c)** — the ⟺ reformulation checked in outline (⇐ uses that cV is JBW and
U_c = proj normal); bidual paragraph is commentary, not a claim. Not on REC's path.

**Overall: STANDS.** No break found. Lemmas to build: `IsNormallyPurelyExceptional`;
`isNormal_comp` (normal ∘ monotone-normal); `isNormal_of_le` (domination, positive-functional
form); `isNormal_jQ` (N1, incl. the [0,1] reduction); `exists_normal_state_pos`;
`opC_normal` (N3); `corner_absurd_normal`; `assoc_absurd_normal`, `npe_exists_exch_pair`;
`corner_purelyExceptional_normal` / `corner_of_summand_normal`; `summand_absurd_normal`;
`rec135_unconditional`; `rec136_unconditional`. Estimate ~750 lines is plausible; the
associative case shrinks (no Gelfand). Residual risks are Lean-engineering only: coercion of
`Φ ξ` on the completion (`opC_coe`, `inner_coe`) and stating N1 for `V →ₗ ℝ` positives.
