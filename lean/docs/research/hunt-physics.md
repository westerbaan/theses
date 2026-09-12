# Hunt: physics consequences of the effectus axioms

Fable, 2026-09-12; thinking only, no Lean, unaudited. Sources: eff.tex 211, 225 (225VI: a
†-effectus gives SEA axioms S1–S3; 225VIII: S4/S5 and "`p&q = q&p ⟹ asrt_p asrt_q = asrt_q asrt_p`"
open), proc.tex 106III, 127III; `new-monoidal.md` Thm 6–7, Conj 8 (`V₃ ⊗_u V₃ = M₄ᵒᵖ ⊕ M₄ᵒᵖ`, one
summand partially transposed; `ℍ₃(𝕆) ⊗_u B = 0`); `new-categorical-probability.md` §4;
`new-analysis-reconstruction.md` (ii). Notation: `a∘b` Jordan product, `a & b = U_{√a} b`,
correlator of a pairing `E(a,b) := 4ω(ψ₁a & ψ₂b) − 2ω(ψ₁a) − 2ω(ψ₂b) + 1`.

## 1. Tsirelson from `&` — SURVIVED (and it is a Jordan theorem, not a Hilbert one)

**Conj 1.** In an `&`-effectus with a commuting tensor (Thm 6), every CHSH value is `≤ 2√2`.

**Mechanism found.** Two steps, both independent of Hilbert space. (a) *`&` ⟹ Jordan.* In finite dimension with real scalars, `asrt_p` extends affinely to the
order-unit space of predicates, so `Pred X` is a "sequential product space"; van de Wetering
(JMP 2019, *Sequential product spaces are Jordan algebras*; and his effect-theoretic
reconstruction, Compositionality 2019, whose purity axioms are eff.tex's ⋄-clauses) gives an
EJA. This is where the effectus axioms enter, and it is the only place.
(b) *Jordan ⟹ Tsirelson, with no commutation hypothesis at all.* In any EJA with state `ω`,
`⟨x,y⟩_ω := ω(x∘y)` is a symmetric bilinear form with `⟨x,x⟩ = ω(x²) ≥ 0`, so Cauchy–Schwarz
holds. For `A_i, B_j` with `A_i², B_j² ≤ 1` put `B± = B₀ ± B₁`, `C = A₀∘B₊ + A₁∘B₋`:
`ω(C) ≤ ‖B₊‖_ω + ‖B₋‖_ω ≤ √2·√(ω(B₊²)+ω(B₋²)) = √2·√(2ω(B₀²+B₁²)) ≤ 2√2`,
using `(x+y)² + (x−y)² = 2x² + 2y²` (true in any commutative algebra). States separate, so
`C ≤ 2√2·1` is an *operator* inequality in every EJA (checked in `M₂`: `σ_z,σ_x,σ_z,σ_x` give
`C = 0`; `σ_z,σ_z,σ_z,σ_z` give `C = 2`).
(c) *Dictionary.* In a commuting span the images operator-commute, and for operator-commuting
`a,b`: `U_{√a} b = 2√a∘(√a∘b) − a∘b = a∘b` (since `L_b` commutes with `L_{√a}`). So
`ψ₁a & ψ₂b = ψ₁a ∘ ψ₂b` and `E(a,b) = ω((2ψ₁a−1)∘(2ψ₂b−1))`: the effectus correlator *is* the
Jordan correlator, and (b) applies.

**Models.** Spin factors `V_n`: `≤ 2√2` for every pairing, Barnum–Wilce confirmed, and the
bound is *attained* already in `V₃ ⊗_u V₃`'s partially-transposed summand (the transpose is a
Jordan automorphism, so its CHSH set equals the quantum one; for two qubits every block-positive
`W = P + Q^Γ`, Woronowicz, so even the maximal tensor stays at `2√2` — the Barnum–Beigi–Boixo–
Elliott–Wehner theorem in the 2×2 case falls out). **PR boxes are excluded by `&` alone**: a
square state space is not an EJA, hence admits no sequential product satisfying (a)'s axioms.
The Albert algebra: internally `C ≤ 2√2` holds by (b), but more is true — it is **Bell-local**:
the operator-commutant of any non-associative subalgebra is commutative, so any Bob commuting
with a non-classical Alice is classical and CHSH `≤ 2`. Proof for Alice `⊆ ℍ₂(𝕆)` (positions
1,2): `[L_x, L_{e₁}] = [L_x, L_{e₂}] = 0` forces `x` into the Peirce-0/1 spaces of both, i.e.
diagonal; commuting with an off-diagonal `a₁₂` forces `α = β` (`L_{e₁}L_a e₁ = ¼a ≠ ½a`), so the
commutant is `span{e₁+e₂, e₃} ≅ ℝ²`. This is a **rank** phenomenon, not an exceptionality one:
`M₃(ℂ)` is Bell-local for the same reason (`A ⊆ A''` forces `A` commutative when `A' ⊇ M₂`);
CHSH `> 2` needs rank `≥ 4 = 2·2`.

**Sharpest test.** Step (a) needs S4/S5-type clauses that 225VI does not derive from the
†-effectus axioms — 225VIII is exactly the gap. Infinite dimension: (b) is verbatim for
JB-algebras, so only "`&` ⟹ JB" is open there. A refuter would be an `&`-effectus with a
non-Jordan predicate space (none known; vdW forbids it in finite dimension).

## 2. Landauer in effectuses — KILLED as stated, replaced by a pinching identity

**Conj 2 (seed).** Pure maps preserve `D_meas`; the quotient by `p` decreases it by exactly "the
entropy of `p`". **Killers.** (i) `asrt_{½}` is pure and halves the sub-normalised `D`. (ii) In
`Kl(𝒟)`, the quotient by `p` sends `ρ ↦ p·ρ` and `D(pρ‖pτ) = D(ρ‖τ) − Σ_x p^⊥(x)ρ(x)log(ρ(x)/τ(x))`:
the loss depends on `ρ,τ` on `p^⊥`, not on `p`. For the full erasure `X → 1 → X` the loss is
all of `D(ρ‖τ)`, which with `τ` Gibbs is the dissipated free energy — that is the classical
Landauer statement and it is vacuous as effectus content.

**Survivor (Thm 2′, `vNᵒᵖ`, finite-dim).** For a sharp `p`, the quotient/comprehension pair
`{p, p^⊥}` has *D-defect* `δ_p(ρ‖τ) := D(ρ‖τ) − D(pρp‖pτp) − D(p^⊥ρp^⊥‖p^⊥τp^⊥) ≥ 0` (monotonicity
under the Lüders pinching plus ⊕-additivity), and
`δ_p(ρ ‖ 1/d) = S(pinch_p ρ) − S(ρ)`: the D-defect at the tracial reference *is* the Landauer
heat of measuring `p`. `δ_p = 0` iff the pinching is Petz-sufficient for `(ρ,τ)`; for `τ = 1/d`
iff `[ρ,p] = 0`, i.e. iff `p` is ρ-non-disturbing (§4). In `Kl(𝒟)` every `δ_p` is `0`.
**Petz in `&`/† form.** For pure `f = ad_V` the ⋄-dagger `f^†` is the trace dual, and Petz's
recovery for the pair `(f, τ)` is `asrt_τ ∘ f^† ∘ asrt_{f(τ)}^{-1}` (states as effects through
the trace; `asrt_{f(τ)}^{-1}` on the support). In `Kl(𝒟)` this is Bayes inversion. So "D is
preserved ⟺ recoverable" is a †-effectus-shaped statement for tracial objects; its status in
`EJAᵒᵖ` (trace-form dagger of `eja-dagger.md`) is the Albert test in §5.

## 3. No-cloning — one direction survives, the other *is* 225VIII

**Conj 3 (seed).** "duplicable ⟺ all predicates sharp ⟺ `&` commutative". **Killer of the
middle clause:** `Kl(𝒟)` — every `X` is duplicable (`X → X×X` diagonal; Thm 7 says `×` is the
commuting tensor) and `&` is commutative, yet `[0,1]^X` is not all sharp. Corrected:

**Conj 3′.** In an `&`-effectus with a commuting tensor: `X` duplicable ⟺ `&` commutative on
`Pred X`. (⟹) Barnum–Barrett–Leifer–Wilce (PRL 2007) works in any no-signalling composite,
including the commuting tensor: broadcastable ⟹ the states lie in a simplex of jointly
distinguishable states; in `EJAᵒᵖ` that forces `A ≅ ℝⁿ` (n distinguishable pure states = n
orthogonal primitive idempotents summing to `1`, so rank = dim), so `&` commutative. Needs
states to separate predicates. In `vNᵒᵖ` it is 127III. (⟸) A duplicator is a *commuting span*
`X ← X → X` of identities in the predicate direction, i.e. `asrt_p asrt_q = asrt_q asrt_p` for
all `p,q` — which `p&q = q&p` gives **exactly when 225VIII's open implication holds**. So
"`&` commutative ⟹ clonable" is equivalent, over the tensor's universal property, to 225VIII.
**Albert.** `ℍ₃(𝕆) ⊗_u ℍ₃(𝕆) = 0` (Conj 8(a)'s proof runs with `B = ℍ₃(𝕆)`: the commutant of a
unital Albert copy in a simple `C ⊇ ℍ₃(𝕆)` is `ℝ1`). The composite of two Albert systems is
the initial object of `EJAᵒᵖ`, the *empty* system: there is no total map into it, so the
Albert algebra is not merely unclonable — two copies cannot coexist. The internal form (two
operator-commuting unital copies inside one EJA) fails at the first step for the same reason.

## 4. Time: a modular flow from a state — KILLED (Alfsen–Shultz), with a surviving fragment

**Conj 4.** In a †-effectus every faithful normal state has a unique "modular" flow of
†-automorphisms, characterised by an `&`-identity. **Killer: `M_n(ℝ)_sa ∈ EJAᵒᵖ`** (a †-effectus
per `eja-dagger.md`). Its automorphisms are `a ↦ OaOᵀ`, one-parameter groups `e^{tK}` with
`K` antisymmetric; fixing `ω = Tr(ρ·)` needs `[K,ρ] = 0`; for `ρ` with distinct eigenvalues
`K` is diagonal and antisymmetric, so `K = 0`. A generic faithful state has *only the trivial*
invariant flow, while the object it should govern is non-trivial: Takesaki's criterion (an
ω-preserving conditional expectation onto `N` exists iff `N` is σ-invariant) still has content —
`N = span{e, e^⊥}` admits one iff `[ρ,e] = 0` (the pinching is ω-preserving exactly then; any
candidate `E(a) = λ(a)e + μ(a)e^⊥` with `E` positive unital forces `λ,μ` to be the corner
states, which are ω-consistent only if `ρ` commutes with `e`). So the invariant exists, the
flow does not: the flow lives in the W*-envelope `M_n(ℂ)`, whose `ad ρ^{it}` leaves `M_n(ℝ)`
only for scalar `ρ`. This is Alfsen–Shultz's theorem that a state-generated dynamics is a
*dynamical correspondence*, available iff the algebra is complex — and `uniqueness` fails even
in `M_n(ℂ)` (`ad f(ρ)^{it}` all fix `ω`; KMS, not invariance, selects `log ρ`), which
`new-analysis-reconstruction.md` already showed is not an `&`-identity.
**Survivor (Thm 4′).** The centraliser is `&`-definable without any flow:
`a ∈ 𝒜_ω ⟺ ω∘(asrt_a + asrt_{a^⊥}) = ω`, i.e. the Lüders instrument of `a` does not disturb
`ω` (the fixed points of a unital channel with commuting normal Kraus operators `√a, √a^⊥`
form the commutant `{a}'`). Takesaki restricted to centraliser-subobjects is then an
`&`-theorem (the ω-preserving expectation is the pinching), and the modular content an
`&`-effectus sees is exactly "non-disturbance of `ω`" — the same predicate that makes §2's
Landauer defect vanish. Note the naive `ω(a & b) = ω(b & a) ∀b` is *not* the centraliser
(`ρ = diag(1,0)`, `a = diag(1,0)`, `b = |+⟩⟨+|`: `1 ≠ ¼`).

## 5. The Albert algebra as a physical effectus

Tally for `ℍ₃(𝕆)ᵒᵖ`: Tsirelson holds (§1b) and vacuously so — it is Bell-local by rank, like
`M₃(ℂ)`; unclonable and uncomposable — its self-composite is the empty system (§3); no state
generates a flow — automorphisms `F₄` exist as *external* symmetries (derivations `𝔣₄`), but
there is no Hamiltonian-from-state, no KMS, no thermal time (§4; Alfsen–Shultz: exceptional ⟹
no dynamical correspondence); the centraliser and the pinching-Landauer identity of §2/§4 make
sense (spectral theorem, trace form) and are the one place where it behaves like `vNᵒᵖ`. Open
Albert test: Petz recovery. `D` is monotone on EJAs; does `D(f ρ‖f τ) = D(ρ‖τ)` imply
recovery by `asrt_τ ∘ f^† ∘ asrt_{f(τ)}^{-1}` (trace-form dagger)? Petz's proof passes through
the operator-algebra square root; for special EJAs the C*-envelope carries it, for the Albert
algebra there is no envelope, so this is a genuine test of "non-Hilbertian quantum theory"
(Barnum–Graydon–Wilce): a single system with quantum logic and quantum statistics but no
neighbours and no clock.

## Scoreboard and next tests

| # | Conjecture | Verdict | Killer / sharpest test |
|---|---|---|---|
| 1 | Tsirelson from `&` | SURVIVED | Jordan Cauchy–Schwarz; gap is 225VIII (`&` ⟹ S4/S5) |
| 1′ | `&` excludes PR boxes | SURVIVED | vdW: square bit is no EJA |
| 1″ | Albert is Bell-local, by rank | SURVIVED | commutant of `ℍ₂(𝕆)` is `ℝ²`; same for `M₃(ℂ)` |
| 2 | quotient loses "entropy of `p`" | KILLED | `asrt_{½}`; `Kl(𝒟)` loss depends on `ρ,τ` |
| 2′ | D-defect of a sharp test = Landauer heat, zero iff non-disturbing | SURVIVED | `M₂`, `τ = 1/2`: `S(pinch ρ) − S(ρ)` |
| 3 | duplicable ⟺ all sharp | KILLED | `Kl(𝒟)` |
| 3′ | duplicable ⟺ `&` commutative | SURVIVED (⟹ BBLW; ⟸ ≡ 225VIII) | Albert: self-composite `= 0` |
| 4 | state ⟹ unique modular flow | KILLED | `M_n(ℝ)_sa`: only `K = 0`; uniqueness fails in `M_n(ℂ)` |
| 4′ | centraliser = ω-non-disturbance | SURVIVED | Kraus-commutant fixed-point theorem |

Next, no Lean: (i) vdW's axiom list against 225VI + ⋄-purity — if his clauses follow from eff.tex
211, Conj 1 is a theorem of the `&`-axioms in finite dimension; (ii) Petz on `ℍ₃(𝕆)` for a
rank-one pure map; (iii) is every rank-`≤3` EJA Bell-local (`M₂(ℍ)` included)?
