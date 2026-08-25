# The commutation theorem — what it would cost

*Reconnaissance of 2026-08-25, four independent passes: Mathlib's inventory, the
tree's inventory, what the seven blocked statements actually need, and the
shortest correct proof in the literature. Written so that the next person to ask
"why is `intersection_tensor` still open?" gets a costed answer instead of a
shrug.*

Read with [`docs/why-open.csv`](why-open.csv) rows `intersection_tensor` and
`equaliser_lemma`, and `PROVING-LOG.md` session 83, which first established the
equivalence recorded in §1.

---

## 0. The thesis says this one out loud

`a.tex:274`, in the introduction to thesis A:

> I've not just mixed and matched results from the literature, but I tailored a
> thorough treatise of everything that's needed, **including proofs (except
> `intersection-tensor-proof`)**.

`intersection-tensor-proof` is the single exception in the whole of thesis A.
`proc.tex:4473` is one line — *"Proof. See Corollary IV.5.10 of [Takesaki1]."*
The one point the thesis declines to prove is the one point still blocking us.
That is a fact about the subject, not about the formalization.

## 1. Everything blocked is blocked on one theorem

Seven `sorry`s remain in `Theses/A/Proc/QuantumLambda.lean`:

| point | name | line |
|---|---|---|
| 121II | `intersection_tensor` | :314 |
| 125IV | `equaliser_lemma` | :2032 |
| 125VI | `tensor_equalisers` | :2060 |
| 125VIIb | `tensor_preimage` | :2085 |
| 125VIII | `tensor_closed` | :2116 |
| 125eIIa | `tensor_map_factorisation` | :4727 |
| 125eIII | `tensorBsurjectivity` (`mpr` only) | :4758 |

121II is Takesaki I, Cor. IV.5.10, and is **equivalent** to Thm IV.5.9, the
commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'`, given the double commutant theorem —
which we have. Both directions re-verified independently on 2026-08-25:

* *IV.5.9 ⟹ IV.5.10*: `(𝒜₁⊗̄ℬ₁) ∩ (𝒜₂⊗̄ℬ₂) = ((𝒜₁'⊗̄ℬ₁') ∪ (𝒜₂'⊗̄ℬ₂'))'`; the
  generated algebra contains every `𝒜ᵢ'⊗1` and `1⊗ℬⱼ'`, hence equals
  `W*(𝒜₁'∪𝒜₂') ⊗̄ W*(ℬ₁'∪ℬ₂') = (𝒜₁∩𝒜₂)' ⊗̄ (ℬ₁∩ℬ₂)'`; one more commutant
  finishes.
* *IV.5.10 ⟹ IV.5.9*: instantiate at `𝒜₁ = M`, `ℬ₁ = B(𝒦)`, `𝒜₂ = B(ℋ)`,
  `ℬ₂ = N`, using only the elementary amplification case.

## 2. Every escape route is closed, and closed by proof

**A special case will not do.** The only instance the thesis ever uses is
`proc.tex:4938`, `Ã⊗𝒞 = (Ã⊗B(ℋ)) ∩ (𝒜⊗𝒞)`. That looks like a special case
(`ℬ₁ = ⊤`, `𝒜₁ ⊆ 𝒜₂`) but is a *presentation* of the general theorem: 125IV
quantifies over all `𝒜`, so taking `𝒜 = B(𝒦)`, `𝒟 = M ⊗̄ 𝒞` and `h` the
inclusion makes `r_ξ(m⊗c) = ⟨ξ,cξ⟩·m`, hence the generated `Ã` exactly `M`.
**Every instance of the general theorem arises as one of 125IV's.**

**The direction used is the hard one.** `proc.tex:4938` uses
`(Ã⊗B(ℋ)) ∩ (𝒜⊗𝒞) ⊆ Ã⊗𝒞`. The `⊇` inclusion — a generator check, the
`sInf_le` idiom used throughout `haTensorPreimage` — is elementary and is never
what a consumer needs.

**The atomic case is already built and cannot reach these statements.** For
hereditarily atomic `𝒜` the slice-map property is *proved*: `haMem`
(`QuantumLambda.lean:3705`), `haE_of_mem` (:3759), on the matrix-unit slice
`haE` (:3398); from them `haTensorPreimage` (:3811) is 125VIIb and
`haTensorBSurj` (:4554) is the hard half of 125eIII. But the algebra that would
have to be atomic is the **tensored** factor, and all seven statements are
general in exactly that slot. Restricting it is 125dII, a different and
already-proved theorem (`ha_tensor_closed`, :4282).

**Slice maps are a dead end, provably.** The Fubini product
`F(M,N) = {x : (ω⊗id)(x) ∈ N, (id⊗ψ)(x) ∈ M}` satisfies `F(M,N) ⊆ (M'⊗̄N')'` by
an elementary computation and `(M⊗̄N)' ⊆ F(M',N')` in three lines — so
Tomiyama's slice-map theorem and the commutation theorem imply each other.
Tomiyama's own paper (*On the tensor products of von Neumann algebras*, Pacific
J. Math. **30** (1969) 263–270, footnote 1 p. 266) says so explicitly and cites
Tomita for the theorem. Slice maps buy the easy half free and nothing else.

**88VI is not the obstruction.** `double_commutant`
(`A/VN/NormalFunctionals.lean:1740`) holds for an arbitrary unital
∗-subalgebra of any `B(H)` — which is exactly the ambient the commutation
theorem lives in, `B(ℋ⊗𝒦)`. The "only for `B(H)`" caveat recorded at
`Projections.lean:4417` is a *different* gap: the relative bicommutant inside an
abstract algebra. It blocks 64II/65IV, not this.

**`intersection_tensor` has no Lean consumer.** `grep concreteTensor` returns
three hits, all inside its own definition and statement. The "blocked on" edges
in `why-open.csv` are route claims about the *printed* proofs. Closing 121II
would additionally require the concrete↔abstract bridge (§5).

## 3. What exists, and what does not

**Mathlib supplies the vocabulary and almost none of the theory** — roughly
10–15%, all definitional. `VonNeumannAlgebra H` is a bicommutant-closed bundled
`StarSubalgebra` with ~15 lemmas, and is an **isolated leaf**: no other file
mentions it, it has no instances (not even for `B(H)`), and it has **no lattice
structure** — `⊤` and `⊓` are advertised in its own docstring but do not exist,
so our target's `∩` is unwriteable in Mathlib's types. The double commutant
theorem is absent in every generality, as are Kaplansky density, the *completed*
tensor product `H ⊗̄ K`, the ultraweak topology, any predual or trace-class
ideal, states, normal maps, cyclic/separating vectors — and modular theory is
missing at its foundations: no `IsClosable`, no polar decomposition of closed
operators, no Borel functional calculus, no Stone's theorem. One cannot *define*
`S = JΔ^{1/2}` there.

What Mathlib does have and we would use: `Set.centralizer` with a full algebraic
API and `Set.isClosed_centralizer`; WOT as `E →WOT[𝕜] F` with `Ring`,
`StarRing`, `ContinuousStar`, `IsSemitopologicalRing`; the *algebraic* inner
tensor product with `mapL`/`lTensor`/`rTensor` and their adjoints; `cfc`;
Banach–Alaoglu; Cauchy–Goursat for rectangles; the identity theorem.

**The tree is unusually complete below the theorem.** Present and general:
`double_commutant` (88VI); `commutant_basic_1/2/3'`; intrinsic
ultraweak/ultrastrong topologies with `functional_permanence_2/3` proving the
subalgebra topology *is* the induced one; normality ↔ continuity; **Kaplansky
density** (74IV); uw/us completeness and ball compactness; `exists_cyclic_projection`
(`NormalFunctionals.lean:1212`) — the classical `[Sx] ∈ S'` device, for any
∗-subalgebra of `B(H)`; `hilb_tensor_basic_2` (the ONB `{e⊗f}`); the full
`opTensor` calculus; `special_tensor` + `tensor_uniqueness` (the concrete↔abstract
bridge, in pieces); `normal_functional`; `exists_faithful_normal_rep`;
`gns_normal` with a genuine cyclic vector; `Corner A e` for arbitrary
projections.

Absent from the tree: **any faithful normal state on a non-commutative von
Neumann algebra**, hence no cyclic-*and*-separating vector; σ-finiteness;
modular theory (`grep -i 'tomita\|modular'` over `Theses/` returns nothing);
relative double commutant; `(eMe)' = eM'e`; slice maps in general; and any API
at all for `concreteTensor`.

**`B/Dils`'s self-dual machinery is not a shortcut.** `ba_ext_tensor_iso`
(165VI) is about adjointable operators on an *exterior* module tensor product,
not commutants inside a fixed `B(H)`; at `𝒜 = ℬ = ℂ` it degenerates to
`B(H) ⊗̄ B(K) ≅ B(H⊗K)`, the trivial case. The module-theoretic route to a
commutant is Rieffel induction via the **interior** tensor product `X ⊗_ℬ H`,
which does not exist in the tree and would be a project of the same order.

The one thing worth harvesting from `B/Dils` is not module theory at all:
`Stinespring.lean` has the **ket/slice operator API** that `A/Proc` lacks —
`hilbTensorKet` (:1203), `hilbTensorKet_adjoint_mk` (:1213),
`conjOperator_ketAdjoint` (:1326) — built for a *different* Hilbert tensor
product, transportable along `hilb_tensor_unique` (`Tensor.lean:693`).

## 4. The route, if we take it

**Not** classical Tomita–Takesaki: that needs closed unbounded operators, their
polar decomposition, the spectral theorem, and product spectral measures — a
Mathlib-scale project before one touches modular theory.

**Not** the semifinite/Hilbert-algebra route: it cannot reach type III, and the
only bridge is Takesaki's structure theorem, itself built on modular theory.

**Rieffel–van Daele**, *A bounded operator approach to Tomita–Takesaki theory*,
Pacific J. Math. **69** (1977) 187–221 (open access, msp.org). Proves
`JMJ = M'` with **no unbounded operators anywhere**: `J` and `Δ^{it}` are built
from the two projections onto `closure(M_sa ω)` and its `i`-rotate.

Only the *conjugation* half `JMJ = M'` is needed. Not needed: the modular
automorphism group as a theory, KMS, weights, left Hilbert algebras, the
standard form, Connes cocycles. Cyclic and separating vectors are not assumed —
they are manufactured by an elementary amplify-and-cut reduction (Zorn for
σ-finite corners; `[M'ξ]` has central carrier 1).

| piece | lines |
|---|---|
| unbounded scaffolding (closed operators, adjoints, `ran(T±i)` criterion, uniqueness of polar decomposition) | 600–1200 |
| RvD §2 — `P,Q,R,T,J`, Prop. 2.2 | 500–900 |
| `R^{it}` for injective positive bounded `R` (avoidable without Borel calculus) | 250–450 |
| RvD §3 to Prop. 3.7 | 700–1200 |
| RvD §4, Lemmas 4.3–4.9 and Thm 4.2 — the analytic core | 1500–2500 |
| RvD appendix: identify `S_ω` with `J·b a^{-1}` | 300–600 |
| tensor factorisation `J_ξ = J_ω ⊗ J_{ω'}` | 600–1000 |
| the reduction to the cyclic-separating case | 1500–2500 |
| amplification theorem, `B(L₁)⊗̄B(L₂) = B(L₁⊗L₂)`, flip/associator transport | 800–1500 |
| IV.5.10 from IV.5.9, plus the concrete↔abstract bridge | 400–800 |
| **total** | **≈ 7 000 – 12 000** |

Two to four months. About a third is the RvD analytic core, a third the
reduction and the tensor plumbing, a third an unbounded-operator layer Mathlib
does not have.

### The one thing to check before anyone starts

The step `J_ξ = J_ω ⊗ J_{ω'}` classically needs the spectral theorem for
unbounded operators and product spectral measures — the single place the bounded
strategy could fail. A bounded substitute was proposed on 2026-08-25 **and is
flagged as a reconstruction, not a citation**:

> With `a := (R/2)^{1/2}`, `b := ((2−R)/2)^{1/2}` — commuting positive
> injective, `a²+b² = 1`, `Δ^{1/2} = b a^{-1}` on `ran a` — the operator
> `T₀ := Δ_ω^{1/2} ⊙ Δ_{ω'}^{1/2}` on `ran(a) ⊙ ran(a')` satisfies
> `(T₀ ± i)(aζ ⊗ a'ζ') = (b⊗b' ± i·a⊗a')(ζ⊗ζ')`, so `ran(T₀±i)` is dense once
> `ker(b⊗b' ∓ i·a⊗a') = 0`; and
> `(b⊗b' ∓ i a⊗a')^*(b⊗b' ∓ i a⊗a') = (b⊗b')² + (a⊗a')² ≥ (a⊗a')²`, injective
> because a tensor product of injective bounded operators is injective. Hence
> `closure(T₀)` is self-adjoint, and uniqueness of polar decomposition gives the
> factorisation.

If this is right it removes the only step that genuinely needed the unbounded
spectral theorem. If it is wrong, the project stops being "hard but finite" and
becomes a Mathlib-scale analysis undertaking. **It is being independently
checked; do not budget against it until that lands.**

## 5. Worth building either way

These are consumed by every route and have value on their own:

1. **The amplification theorem** `(M ⊗ 1)' = M' ⊗̄ B(𝒦)` — session 83's step
   (E), the one unqualifiedly elementary case. Its `⊆` half is
   `wstar_opTensor_comm` (`Tensor.lean:9095`, private) plus uw-closedness of a
   commutant; its `⊇` half needs the ket/slice API described in §3.
2. **`concreteTensor`'s API and the concrete↔abstract bridge.** Without it a
   proved 121II would close nothing. `special_tensor` (111VII) plus
   `tensor_uniqueness` (114II) should give
   `VNSub _ (concreteTensor H K SA SB) ≅ VNT (VNSub _ SA) (VNSub _ SB)`.
3. **One factor atomic type I**, `N ≅ ⊕_j B(𝒦_j)`: matrix units give the
   slice-map property directly. This is the existing `haE` device with `M_{n_j}`
   widened to `B(𝒦_j)`, and it strictly extends the reach of 125dII/125eVII.
4. **Both algebras finite with cyclic trace vectors**: here `J` is *bounded*
   (`‖x*ω‖² = τ(xx*) = τ(x*x) = ‖xω‖²`), `JMJ = M'` is the Murray–von Neumann
   argument, and `J_{ω⊗ω'} = J_ω ⊗ J_{ω'}` is immediate — two bounded
   conjugations agreeing on a total set. A genuine, if restricted, commutation
   theorem for ~800–1200 lines.

None of 1–4 closes any of the seven as stated. 3 widens the atomic branch.

## 6. Already banked

`96e34ef` — **125eIII is half proved.** The `mp` direction needs neither the
`(·)⊗ℬ`-surjectivity hypothesis nor atomicity: it is `proc.tex:5620` via
`tmapM_range_le` and 69IVb `nmiu_image`, fifteen lines, machine-checked in full
generality. The remaining `sorry` is exactly `mpr` (`proc.tex:5600`), which
needs 125VIIb. The CSV row had the two directions **inverted** relative to the
Lean iff; corrected.

## Sources

Rieffel & Van Daele, *A bounded operator approach to Tomita–Takesaki theory*,
Pacific J. Math. **69** (1977) 187–221 — full text read. Rieffel & Van Daele,
*The commutation theorem for tensor products of von Neumann algebras*, Bull.
LMS **7** (1975) 257–260 — **abstract only, full text not obtained**; its Thm 1
is quoted in the 1977 paper's Prop. 4.1. Tomiyama, Pacific J. Math. **30**
(1969) 263–270 — full text read. Takesaki, *Theory of Operator Algebras I*,
Thm IV.5.9 / Cor. IV.5.10; *Tomita's Theory of Modular Hilbert Algebras*, LNM
128 (1970). Kadison–Ringrose II, chs. 9 and 11 — chapter titles verified,
theorem numbers not.
