# Research notes

Exploratory notes written by Fable agents on 2026-09-12, at the author's
request, each with statements, sketches and refutation targets.  They are
*not* audited: nothing here is in the Lean tree or in the theses, and every
claim should be treated as a conjecture with a sketch until checked.

Starting from the week's discussion:

* `support-order.md` — the preorder `f ⊑ g ⟺ f^⋄ ≤ g^⋄`; sums as joins in any ⋄-effectus; rigidity of pure maps reduced to rigidity of quotients; an object-wise centre and a Radon–Nikodym conjecture; axioms for an abstract Paschke correspondence.
* `modules-as-corners.md` — self-dual Hilbert modules as corners `(1−e)Le` of a von Neumann algebra `L` with `eLe ≅ ℬ`; 150II as an ultrastrong closure, 152X as the bicommutant theorem, 159IV and tensor products as corner statements.
* `purity.md` — purity as "rigidity plus injectivity of the normalisation"; B15 beyond `vN`; square roots in `Kl(𝒟)`.
* `eja-dagger.md` — `EJAᵒᵖ` as an `&`-effectus (no fundamental formula needed) and †-effectus (axiom 2 *is* the fundamental formula; a tree-native route); the trace-form dagger; Murray–von Neumann equivalence via symmetries.

Going out on a limb:

* `new-categorical-probability.md` — Paschke dilations as disintegration; no-information-without-disturbance from eff 221–223; the Markov core of `vNᵒᵖ`; `Kl(Giry)` has no images; measured relative entropy as the least monotone extension of KL.
* `new-semantics-logic.md` — `vNᵒᵖ` is `DCPO⊥`-enriched but the quantum lambda model's function type does not see the order; effect-level `wp`/`wlp`; an affine MELL model; subset and co-subset types.
* `new-analysis-reconstruction.md` — `[0,1]_E` is a sequential effect algebra for every EJA; centraliser and factor type as `&`-notions; reconstruction through Alfsen–Shultz; a corrected clause (E) for 106III.3.
* `new-wildcard.md` — pure maps as projective-geometry morphisms in both directions; Paschke objects as transport plans; confusability systems; Frigerio irreducibility as a ⋄-notion.

Second round, further out (2026-09-12, later):

* `new-morita.md` — the Paschke module as the initial pointed correspondence over `φ`; composition of dilations only colax (Bhat–Skeide); effectus Morita equivalence recovers Rieffel's in `vNᵒᵖ`, sees only the centre in `EJAᵒᵖ`, which is not Morita-closed.
* `new-base.md` — Kadison's two axioms are exactly quotients/comprehension and images: `vNᵒᵖ = ⋄-effectus + state-separation`; `A ↦ A**` a coreflection; no eff.tex axiom sees the field, a local qubit axiom does; `JBWᵒᵖ` on one Jordan division lemma.
* `new-metric.md` — `p ↦ asrt_p` is exactly ½-Hölder in cb-norm, Lipschitz iff commutative; approximate comprehension at `√η`; ε-sharpness stable, ⋄-based ε-purity not; Kaplansky as an intrinsic density notion; a `⊗`-free simulation distance.
* `new-monoidal.md` — monoidal effectuses and the tensor question 222IV; free effectuses; partial traces: the phase group Φ(s) of a sharp predicate (U(1) in vNᵒᵖ, trivial in Kl(𝒟), O(n−1) for spin factors) answers 222IV's CNOT question; the spatial tensor is not internal (Effros–Lance); Kl(𝒟_M)_fin is the initial effectus with scalars Mᵒᵖ; Par(vNᵒᵖ) is ⊕-traced only.

Wild hunts (2026-09-12, later still; each conjecture attacked before being reported):

* `hunt-ktheory.md` — `K₀` of an effectus (sharp predicates modulo symmetry exchange) matches `K₀` of the algebra; a Möbius/Lefschetz number of the lattice of `f^⋄`-invariant sharp predicates separates real from complex quantum theory; quotient/comprehension as a kernel–cokernel pair with the Peirce-½ dimension as the additivity defect.
* `hunt-topos.md` — Bohrification, internal `Kl(𝒟)`, Ozawa transfer and "Markov effectuses are `Kl(𝒟)`-like" all killed; survivors: images over a base space iff basically disconnected, and a counital copy map forces Boolean sharp predicates.
* `hunt-physics.md` — Tsirelson is a Jordan theorem (Cauchy–Schwarz on `ω(x∘y)`), so `&`-effectuses exclude PR boxes; the Albert algebra is Bell-local, unclonable, uncomposable, clockless; Landauer as seeded killed, replaced by a pinching identity; modular time killed by `M_n(ℝ)`.
* `hunt-transfer.md` — the commutative transfer principle dies at `p & q = q & p`, the Jordan one at Glennie's `G₈`; every effect algebra of size ≤ 4 occurs; the † axiom forces real-closed, never Archimedean, scalars.
* `review-rec104.md` — break-it review of REC §5: the REC 104 refutation stands (states are total maps as printed); rec102/103 are faithful modulo their named hypotheses.
* `as948-reformulation.md` — `AlfsenShultzJordanFromDerivations` is REC's transplant of the A–S 9.43/9.48 argument without spectral duality, not an instance of the literal theorem; no derivation known, truth open. Reviewed: the proposed split's H1 must read `[D_i,D_j]1 = 0`, and the split is equivalent, not weaker; no erratum for "commutativity of the T_p" (short.tex:2233 defines it).
* `review-rec136.md` — break-it review of REC §6: all named hypotheses faithful (the A–S *Geometry* Lemma 4.4 label for REC 132 verified in `rec-citations.md`); rec136 as printed; REC 127's zero-object refutation stands but is not an erratum; the triple-product swap is.
* `as948-discharge.md` — in REC's own setting the symmetry `[D_p,D_q]1 = 0` holds in the Peirce-1/0 corners of `p`, `q` (from REC 119 via comprehensions); the Peirce-½ component could not be derived (corner data provably cannot decide it) and no counter-model is known. Reviewed: Lemma A needs the total-state repair; ERRATA REC 121 filed.
* `as948-lemmaM.md` — the Jordan symmetry `[D_p,D_q]1 = 0` follows from REC 120 plus "commutators of order derivations are order derivations": `x` is killed by `D_p`, `D_q`, so `e^{t[D_p,D_q]}1 = 1 + 4tx`, and positivity gives `x = 0`. Survived a break-it review; supersedes the open verdict of `as948-discharge.md`.
* `as943-transplant.md` — the rest of A–S 9.43 (continuity, Jordan identity, order axiom) follows given chain density with commuting members (G1+G2), which REC's V_A has; open for the abstract Prop. Reviewed: go, with G1 from a rewritten spectral list.
* `rec-citations.md` — REC's external citations checked against the sources: A–S *Geometry* Lemma 4.4, 9.43, 9.48, *State spaces* (1.82), 1.106, 1.108, 1.114, H-O–S 7.2.7, van de Wetering Prop 46 verified; REC 55 is Shultz 1979 Thm 3.9; the vdW paper is *Sequential product spaces are Jordan algebras* (arXiv:1803.11139v3). Lean docstring fixes pending (§5 items 1–5).
