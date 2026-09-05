/-
Thesis B, chapter "Effectuses" (eff.tex): **the von Neumann examples**.

Every statement in this file is an *example* asserting that the concrete
category `vNᵒᵖ` — `WStarNCPU.{u}ᵒᵖ` in total form, `WStarCPSU.{u}ᵒᵖ` in
partial form — carries one of the structures the chapter defines, or that
the effects / projections of a von Neumann algebra carry one of its
algebraic structures.  They are therefore the only points of the effectus
chapter whose proofs need the von Neumann theory of **thesis A** and the
Paschke dilations of **B/Dils**.

## Why this file exists (author ruling, 2026-08-17)

The other eight files of `Theses/B/Eff/` import **only** `Theses.Common`,
which keeps the whole effectus development independent of the
`A/CStar → A/VN → {A/Proc, B/Dils}` chain: they build fast and cannot be
broken by work upstream.  Rather than give that up by importing thesis A
into `Effectus.lean`, `Dagger.lean`, … the author ruled that the
A-dependent statements live here, in a single leaf module.  Only this file
sees thesis A, and only this file is exposed to churn in it.

`Theses.B.Dils.Pure` transitively supplies all of `A/CStar`, all of `A/VN`
and all of `B/Dils`.  **`Theses.A.Proc.Measurement` is imported too**:
`vn_has_dilations` (221III) needs *sharp + total ⟹ nmiu*, which eff.tex:4779
proves by citing `sharp-multiplicative` = **99XII** (proc.tex:905), and that
is proved there.  The import is cheap and safe — `Measurement.lean` imports
only `Theses.A.VN.NormalFunctionals`, which `B/Dils` already supplies, so it
adds one file and a few seconds; and it is made **here only**, so the other
eight files of `Theses/B/Eff/` still import `Theses.Common` alone.
(`Measurement.lean` carries one `sorry` of its own,
`sequential_product_counterexample_3`; nothing used from it here touches
that.  Since 2026-09-05 this file uses a good deal of `Measurement.lean` —
`square_f`, `pure_fundamental`, `gardner`, `iso`, `sharp_multiplicative`, the
spectral projections of 104VII — and every declaration here that does so is
`#print axioms`-clean.)

It also carries **195V.5**'s `L^∞` half (eff.tex:3275): the effect monoid on
the unit interval of `L^∞[0,1]` *is* an effect divisoid.  That clause needs
`L^∞`, which exists in the tree only as thesis A's `Linfty μ`, so it cannot
sit next to its `C[0,1]` twin (`cIcc_unitInterval_not_divisoid`, 195V.5's
first half) in `B/Eff/StatesPredicates.lean`.  See the section at the end of
this file.

`vn_is_andthen_eff` (211IV) is proved in eff.tex:4859 from **105V**
`positive-map-uniqueness` and **100III** `pure-fundamental`, both in
`Theses/A/Proc/Measurement.lean` and both proved and axiom-clean there.  What
it used to wait on was **QUESTIONS B15**, a definitional mismatch between the
two theses over whether the ⋄-self-adjoint square root of a ⋄-positive map is
required to be pure; since 2026-09-05 it waits on nothing — in `vNᵒᵖ` the two
classes provably agree (`docs/B15-S.md`, formalized in the section
`B15SquareRoot` below).  B15 stays open as a question about the wording of
206II.4 only.  See the doc comment on `vn_is_andthen_eff` itself.
-/
import Theses.B.Eff.Comparisons
import Theses.B.Dils.Pure
import Theses.A.Proc.Measurement

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

/-! ## The trivial von Neumann algebra (infrastructure)

`effectus_vn` needs `HasFiniteCoproducts vNᵒᵖ`, hence an *initial* object of
`vNᵒᵖ`, i.e. a **terminal** object of `vN` — the trivial algebra `{0}`,
which 8II of thesis A explicitly admits.  `CStarAlgebra PUnit` does not
synthesize, but only because the four instances below are missing from
Mathlib; **`CStarAlgebra` extends `NormedRing`, not `NormOneClass`**, so
nothing about the trivial algebra is actually excluded.  (Mathlib does
already have one trivial C\*-algebra by accident:
`CStarAlgebra (Π _ : Empty, ℂ)` synthesises from the finite-`Pi` instance.)

With these, `WStar.trivial` is a bona fide object of `WStarNCPU`/`WStarCPSU`.
That it is final in `vN` (hence initial in `vNᵒᵖ`) is `vnTrivIsTerminal`
below, and `suTrivIsTerminal` for the ncpsu-maps. -/

section TrivialAlgebra

instance : StarRing PUnit.{u + 1} where
  star := id
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl

instance : CStarRing PUnit.{u + 1} where
  norm_mul_self_le _ := le_of_eq (by simp)

instance : StarModule ℂ PUnit.{u + 1} where
  star_smul _ _ := rfl

noncomputable instance : CStarAlgebra PUnit.{u + 1} := {}

instance : StarOrderedRing PUnit.{u + 1} :=
  StarOrderedRing.of_le_iff fun _ _ =>
    ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => le_of_eq (Subsingleton.elim _ _)⟩

instance : Theses.VonNeumannAlgebra PUnit.{u + 1} where
  isLUB_of_bddAbove_directed _ _ _ _ :=
    ⟨0, ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
        fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩⟩
  np_faithful _ _ _ := Subsingleton.elim _ _

/-- The trivial von Neumann algebra `{0}` as an object of `WStar`: the
terminal object of `vN`, hence the initial object of `vNᵒᵖ`. -/
noncomputable def WStar.trivial : WStar.{u} := WStar.of PUnit.{u + 1}

end TrivialAlgebra


/-! ## Projections of a von Neumann algebra (parsec 177)

The A-dependent statements of `EffectAlgebras.lean`. -/

section ProjLattice

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Theses.VonNeumannAlgebra A]

/-- Both members of `{p, q}` are projections. -/
private theorem pair_proj {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : ∀ x ∈ ({p, q} : Set A), IsStarProjection x := by
  intro x hx
  rcases hx with rfl | hx
  · exact hp
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hq

/-- The join of two projections in the poset of projections, `⋃{p,q}` of
**56XVI**. -/
private noncomputable def pjoin (p q : { p : A // IsStarProjection p }) :
    { p : A // IsStarProjection p } :=
  ⟨Theses.A.VN.projSup {p.1, q.1},
    (Theses.A.VN.projSup_spec (pair_proj p.2 q.2)).1⟩

private theorem le_pjoin_left (p q : { p : A // IsStarProjection p }) :
    p ≤ pjoin p q :=
  (Theses.A.VN.projSup_spec (pair_proj p.2 q.2)).2.1 p.1 (Or.inl rfl)

private theorem le_pjoin_right (p q : { p : A // IsStarProjection p }) :
    q ≤ pjoin p q :=
  (Theses.A.VN.projSup_spec (pair_proj p.2 q.2)).2.1 q.1
    (Or.inr rfl)

private theorem pjoin_le {p q r : { p : A // IsStarProjection p }} (hp : p ≤ r)
    (hq : q ≤ r) : pjoin p q ≤ r := by
  refine (Theses.A.VN.projSup_spec (pair_proj p.2 q.2)).2.2 r.1 r.2 ?_
  intro x hx
  rcases hx with rfl | hx
  · exact hp
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hq

/-- **Key computation**: the join of two *orthogonal* projections is their
sum.  This is the **binary instance** of **55XIII**.2
(`orthogonal-tuple-of-projections`, vn.tex:2334, Exercise) — that for a
pairwise orthogonal *finite* tuple `p₁, …, pₙ` the sum `∑ᵢ pᵢ` is the least
projection above them all.  The point itself is proved in thesis A, as
`Theses.A.VN.orthogonal_tuple_of_projections_2'`, and it is exactly what is
applied here at `n = 2`; this private helper only transports it to
`Theses.A.VN.projSup {p, q}`. -/
private theorem pjoin_of_orthogonal {p q : { p : A // IsStarProjection p }}
    (hpq : p.1 * q.1 = 0) : (pjoin p q).1 = p.1 + q.1 := by
  have hqp : q.1 * p.1 = 0 :=
    ((Theses.A.VN.orthogonal_tuple_of_projections_1 p.1 q.1 p.2 q.2).out 0 1).mp hpq
  have hfam : ∀ i, IsStarProjection (![p.1, q.1] i) := by
    intro i; fin_cases i
    · exact p.2
    · exact q.2
  have horth : Pairwise fun i j => ![p.1, q.1] i * ![p.1, q.1] j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hleast := Theses.A.VN.orthogonal_tuple_of_projections_2' ![p.1, q.1] hfam horth
  rw [Fin.sum_univ_two] at hleast
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hleast
  refine Theses.A.VN.projSup_eq (pair_proj p.2 q.2) hleast.1.1 ?_ ?_
  · intro x hx
    rcases hx with rfl | hx
    · exact hleast.1.2 0
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hleast.1.2 1
  · intro r hr hub
    refine hleast.2 ⟨hr, ?_⟩
    intro i
    fin_cases i
    · exact hub p.1 (Or.inl rfl)
    · exact hub q.1 (Or.inr rfl)

/-- The orthocomplement `pᶜ = 1 - p`. -/
private def pcompl (p : { p : A // IsStarProjection p }) :
    { p : A // IsStarProjection p } :=
  ⟨1 - p.1, p.2.one_sub⟩

private theorem pcompl_pcompl (p : { p : A // IsStarProjection p }) :
    pcompl (pcompl p) = p :=
  Subtype.ext (sub_sub_cancel 1 p.1)

/-- The meet, by De Morgan. -/
private noncomputable def pmeet (p q : { p : A // IsStarProjection p }) :
    { p : A // IsStarProjection p } :=
  pcompl (pjoin (pcompl p) (pcompl q))

private theorem pcompl_antitone {p q : { p : A // IsStarProjection p }}
    (h : p ≤ q) : pcompl q ≤ pcompl p :=
  Subtype.coe_le_coe.mp (sub_le_sub_left (Subtype.coe_le_coe.mpr h) 1)

private theorem pmeet_le_left (p q : { p : A // IsStarProjection p }) :
    pmeet p q ≤ p := by
  have := pcompl_antitone (le_pjoin_left (pcompl p) (pcompl q))
  rwa [pcompl_pcompl] at this

private theorem pmeet_le_right (p q : { p : A // IsStarProjection p }) :
    pmeet p q ≤ q := by
  have := pcompl_antitone (le_pjoin_right (pcompl p) (pcompl q))
  rwa [pcompl_pcompl] at this

private theorem le_pmeet {p q r : { p : A // IsStarProjection p }} (hp : r ≤ p)
    (hq : r ≤ q) : r ≤ pmeet p q := by
  have h := pcompl_antitone (pjoin_le (pcompl_antitone hp) (pcompl_antitone hq))
  rwa [pcompl_pcompl] at h

/-- `p ⊔ pᶜ = 1`: the two are orthogonal and sum to `1`. -/
private theorem pjoin_pcompl_self (p : { p : A // IsStarProjection p }) :
    (pjoin p (pcompl p)).1 = 1 := by
  have horth : p.1 * (pcompl p).1 = 0 := p.2.mul_one_sub_self
  rw [pjoin_of_orthogonal horth]
  show p.1 + (1 - p.1) = 1
  abel

end ProjLattice

/-- **177V** (eff.tex:559, Example): the lattice of projections of a von
Neumann algebra is an orthomodular lattice with `pᶜ = 1 - p`.

Both of the point's data are **in the statement**: the orthomodular lattice
is one *for the order the projections inherit from `𝒜`* (its
`PartialOrder` is literally the ambient one, first conjunct), and its
orthocomplement is literally `p ↦ 1 - p` (second conjunct).  A bare
`Nonempty (OrthomodularLattice {p // IsStarProjection p})` would assert
neither, since `Ortholattice extends Lattice` carries an order of its own;
and once the order is pinned the meet and join are pinned with it, being
determined by the order.

The join is `⋃{p,q}` of **56XVI** (`Theses.A.VN.projSup`, proved in thesis
A); the meet is its De Morgan dual.  Orthomodularity comes down to
**55XIII**.2, that the sum of two orthogonal projections is their *least*
upper bound among projections: for `p ≤ q` one computes `pᶜ ⊓ q = q - p`
and then `p ⊔ (q - p) = p + (q - p) = q`. -/
theorem projections_orthomodularLattice (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    ∃ L : OrthomodularLattice { p : A // IsStarProjection p },
      L.toOrtholattice.toLattice.toSemilatticeInf.toPartialOrder
          = (inferInstance : PartialOrder { p : A // IsStarProjection p }) ∧
        ∀ p : { p : A // IsStarProjection p },
          ((L.toOrtholattice.toCompl.compl p : { p : A // IsStarProjection p })
            : A) = 1 - (p : A) := by
  letI lat : Lattice { p : A // IsStarProjection p } :=
    { (inferInstance : PartialOrder { p : A // IsStarProjection p }) with
      sup := pjoin
      le_sup_left := le_pjoin_left
      le_sup_right := le_pjoin_right
      sup_le := fun _ _ _ h₁ h₂ => pjoin_le h₁ h₂
      inf := pmeet
      inf_le_left := pmeet_le_left
      inf_le_right := pmeet_le_right
      le_inf := fun _ _ _ h₁ h₂ => le_pmeet h₁ h₂ }
  letI bo : BoundedOrder { p : A // IsStarProjection p } :=
    { top := ⟨1, IsStarProjection.one A⟩
      bot := ⟨0, IsStarProjection.zero A⟩
      le_top := fun p => p.2.le_one
      bot_le := fun p => p.2.nonneg }
  letI cpl : Compl { p : A // IsStarProjection p } := ⟨pcompl⟩
  refine ⟨{ inf_compl := ?_, sup_compl := ?_, compl_antitone := ?_,
            compl_compl := ?_, orthomodular := ?_ }, rfl, fun _ => rfl⟩
  · intro a
    show pmeet a (pcompl a) = _
    have h : pmeet a (pcompl a) = pcompl (pjoin (pcompl a) a) := by
      show pcompl (pjoin (pcompl a) (pcompl (pcompl a))) = _
      rw [pcompl_pcompl]
    rw [h]
    refine Subtype.ext ?_
    show 1 - (pjoin (pcompl a) a).1 = 0
    have := pjoin_pcompl_self (pcompl a)
    rw [pcompl_pcompl] at this
    rw [this, sub_self]
  · intro a
    exact Subtype.ext (pjoin_pcompl_self a)
  · intro a b h
    exact pcompl_antitone h
  · intro a
    exact pcompl_pcompl a
  · intro a b hab
    -- `aᶜ ⊓ b = b - a`
    have hmul : a.1 * b.1 = a.1 := (a.2.le_iff_mul_eq_left b.2).mp hab
    have horth1 : a.1 * (pcompl b).1 = 0 := by
      show a.1 * (1 - b.1) = 0
      rw [mul_sub, mul_one, hmul, sub_self]
    have hstep : pmeet (pcompl a) b = ⟨b.1 - a.1, ((a.2.le_iff_sub b.2).mp hab)⟩ := by
      refine Subtype.ext ?_
      show 1 - (pjoin (pcompl (pcompl a)) (pcompl b)).1 = b.1 - a.1
      rw [pcompl_pcompl, pjoin_of_orthogonal horth1]
      show 1 - (a.1 + (1 - b.1)) = b.1 - a.1
      abel
    show pjoin a (pmeet (pcompl a) b) = b
    rw [hstep]
    refine Subtype.ext ?_
    have horth2 : a.1 * (b.1 - a.1) = 0 := by
      rw [mul_sub, hmul, a.2.isIdempotentElem.eq, sub_self]
    rw [pjoin_of_orthogonal (q := ⟨b.1 - a.1, ((a.2.le_iff_sub b.2).mp hab)⟩) horth2]
    show a.1 + (b.1 - a.1) = b.1
    abel

/-! ## Infrastructure for the von Neumann effectus (180V)

Everything `effectus_vn` needs that is not already in the tree: products and
the scalars `ℂᵤ = ULift ℂ` as von Neumann algebras, a hand-built API for
ncpu-maps (the identity and composition of `WStarCat.lean` are obtained by
`Classical.choice`, so their defining equations are propositional rather than
definitional), the concrete presentation `vnPres` of `vNᵒᵖ`, and the two
pushout squares and the joint-monicity statement of 180I. -/

section VNEffectus

open Theses.A.CStar
open scoped ComplexOrder ComplexStarModule

section VNInfra

/-! ### Products of von Neumann algebras -/

section ProdVNA

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

set_option linter.unusedSectionVars false in
theorem prod_sa_fst {x : A × B} (hx : IsSelfAdjoint x) : IsSelfAdjoint x.1 :=
  congrArg Prod.fst hx

set_option linter.unusedSectionVars false in
theorem prod_sa_snd {x : A × B} (hx : IsSelfAdjoint x) : IsSelfAdjoint x.2 :=
  congrArg Prod.snd hx

/-- First component of a self-adjoint element of a product. -/
def saFst (x : selfAdjoint (A × B)) : selfAdjoint A := ⟨x.1.1, prod_sa_fst x.2⟩

/-- Second component of a self-adjoint element of a product. -/
def saSnd (x : selfAdjoint (A × B)) : selfAdjoint B := ⟨x.1.2, prod_sa_snd x.2⟩

theorem saFst_mono {x y : selfAdjoint (A × B)} (h : x ≤ y) : saFst x ≤ saFst y :=
  Subtype.coe_le_coe.mp (Prod.le_def.mp (Subtype.coe_le_coe.mpr h)).1

theorem saSnd_mono {x y : selfAdjoint (A × B)} (h : x ≤ y) : saSnd x ≤ saSnd y :=
  Subtype.coe_le_coe.mp (Prod.le_def.mp (Subtype.coe_le_coe.mpr h)).2

theorem sa_le_of_components {x y : selfAdjoint (A × B)} (h₁ : saFst x ≤ saFst y)
    (h₂ : saSnd x ≤ saSnd y) : x ≤ y :=
  Subtype.coe_le_coe.mp (Prod.le_def.mpr
    ⟨Subtype.coe_le_coe.mpr h₁, Subtype.coe_le_coe.mpr h₂⟩)

/-- The first component of a supremum in a product is the supremum of the
first components (the upper bounds of a set in a product order are exactly
the pairs of componentwise upper bounds). -/
theorem isLUB_saFst {D : Set (selfAdjoint (A × B))} {s : selfAdjoint (A × B)}
    (h : IsLUB D s) : IsLUB (saFst '' D) (saFst s) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact saFst_mono (h.1 hd)
  · intro x hx
    have hsa : IsSelfAdjoint ((x : A), (saSnd s : B)) :=
      Prod.ext x.2 (saSnd s).2
    have hub : (⟨((x : A), (saSnd s : B)), hsa⟩ : selfAdjoint (A × B))
        ∈ upperBounds D := by
      intro d hd
      refine sa_le_of_components (hx ⟨d, hd, rfl⟩) ?_
      have hd2 : saSnd d ≤ saSnd s := saSnd_mono (h.1 hd)
      exact hd2
    exact saFst_mono (h.2 hub)

theorem isLUB_saSnd {D : Set (selfAdjoint (A × B))} {s : selfAdjoint (A × B)}
    (h : IsLUB D s) : IsLUB (saSnd '' D) (saSnd s) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact saSnd_mono (h.1 hd)
  · intro x hx
    have hsa : IsSelfAdjoint ((saFst s : A), (x : B)) :=
      Prod.ext (saFst s).2 x.2
    have hub : (⟨((saFst s : A), (x : B)), hsa⟩ : selfAdjoint (A × B))
        ∈ upperBounds D := by
      intro d hd
      refine sa_le_of_components ?_ (hx ⟨d, hd, rfl⟩)
      have hd1 : saFst d ≤ saFst s := saFst_mono (h.1 hd)
      exact hd1
    exact saSnd_mono (h.2 hub)

theorem directedOn_saFst {D : Set (selfAdjoint (A × B))}
    (h : DirectedOn (· ≤ ·) D) : DirectedOn (· ≤ ·) (saFst '' D) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
  obtain ⟨z, hz, hdz, hez⟩ := h d hd e he
  exact ⟨saFst z, ⟨z, hz, rfl⟩, saFst_mono hdz, saFst_mono hez⟩

theorem directedOn_saSnd {D : Set (selfAdjoint (A × B))}
    (h : DirectedOn (· ≤ ·) D) : DirectedOn (· ≤ ·) (saSnd '' D) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
  obtain ⟨z, hz, hdz, hez⟩ := h d hd e he
  exact ⟨saSnd z, ⟨z, hz, rfl⟩, saSnd_mono hdz, saSnd_mono hez⟩

/-- The np-functional `(a, b) ↦ ω a` on a product. -/
noncomputable def npFst [Theses.VonNeumannAlgebra A] (ω : Theses.NPFunctional A) :
    Theses.NPFunctional (A × B) where
  toPositiveLinearMap :=
    { toLinearMap := (ω.toPositiveLinearMap : A →ₗ[ℂ] ℂ).comp (LinearMap.fst ℂ A B)
      monotone' := fun _ _ h => ω.toPositiveLinearMap.monotone' (Prod.le_def.mp h).1 }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := ω.preservesDirSups' (saFst '' D) (saFst s) (hne.image _)
      (directedOn_saFst hdir) (isLUB_saFst hlub)
    rwa [Set.image_image] at h

/-- The np-functional `(a, b) ↦ ω b` on a product. -/
noncomputable def npSnd [Theses.VonNeumannAlgebra B] (ω : Theses.NPFunctional B) :
    Theses.NPFunctional (A × B) where
  toPositiveLinearMap :=
    { toLinearMap := (ω.toPositiveLinearMap : B →ₗ[ℂ] ℂ).comp (LinearMap.snd ℂ A B)
      monotone' := fun _ _ h => ω.toPositiveLinearMap.monotone' (Prod.le_def.mp h).2 }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := ω.preservesDirSups' (saSnd '' D) (saSnd s) (hne.image _)
      (directedOn_saSnd hdir) (isLUB_saSnd hlub)
    rwa [Set.image_image] at h

/-- **The product of two von Neumann algebras is a von Neumann algebra.**
Suprema of bounded directed sets are computed componentwise (the upper
bounds of a set in a product order form a product), and the np-functionals
`ω ∘ π₁`, `ω ∘ π₂` are jointly faithful. -/
instance instVonNeumannAlgebraProd [Theses.VonNeumannAlgebra A]
    [Theses.VonNeumannAlgebra B] : Theses.VonNeumannAlgebra (A × B) where
  isLUB_of_bddAbove_directed D hne hdir hbdd := by
    obtain ⟨c, hc⟩ := hbdd
    obtain ⟨s₁, hs₁⟩ := Theses.VonNeumannAlgebra.isLUB_of_bddAbove_directed
      (saFst '' D) (hne.image _) (directedOn_saFst hdir)
      ⟨saFst c, by rintro _ ⟨d, hd, rfl⟩; exact saFst_mono (hc hd)⟩
    obtain ⟨s₂, hs₂⟩ := Theses.VonNeumannAlgebra.isLUB_of_bddAbove_directed
      (saSnd '' D) (hne.image _) (directedOn_saSnd hdir)
      ⟨saSnd c, by rintro _ ⟨d, hd, rfl⟩; exact saSnd_mono (hc hd)⟩
    refine ⟨⟨((s₁ : A), (s₂ : B)), Prod.ext s₁.2 s₂.2⟩, ?_, ?_⟩
    · intro d hd
      exact sa_le_of_components (hs₁.1 ⟨d, hd, rfl⟩) (hs₂.1 ⟨d, hd, rfl⟩)
    · intro x hx
      refine sa_le_of_components (hs₁.2 ?_) (hs₂.2 ?_)
      · rintro _ ⟨d, hd, rfl⟩; exact saFst_mono (hx hd)
      · rintro _ ⟨d, hd, rfl⟩; exact saSnd_mono (hx hd)
  np_faithful x hx hω := by
    refine Prod.ext ?_ ?_
    · refine Theses.VonNeumannAlgebra.np_faithful x.1 (Prod.le_def.mp hx).1 fun ω => ?_
      exact hω (npFst ω)
    · refine Theses.VonNeumannAlgebra.np_faithful x.2 (Prod.le_def.mp hx).2 fun ω => ?_
      exact hω (npSnd ω)

end ProdVNA

end VNInfra

section

section ScalarsVNA

/-! ### The scalars `ℂᵤ` as a von Neumann algebra -/

private theorem cu_sa {x : ULift.{u} ℂ} (h : IsSelfAdjoint x) : IsSelfAdjoint x.down :=
  congrArg ULift.down h

private theorem cu_sa' {c : ℂ} (h : IsSelfAdjoint c) :
    IsSelfAdjoint (ULift.up.{u} c) := congrArg ULift.up h

/-- The self-adjoint part of `ℂᵤ`, pushed down to `ℂ`. -/
private def saDown (x : selfAdjoint (ULift.{u} ℂ)) : selfAdjoint ℂ :=
  ⟨x.1.down, cu_sa x.2⟩

/-- The self-adjoint part of `ℂ`, lifted to `ℂᵤ`. -/
private def saUp (c : selfAdjoint ℂ) : selfAdjoint (ULift.{u} ℂ) :=
  ⟨⟨c.1⟩, cu_sa' c.2⟩

private theorem saDown_le_iff {x y : selfAdjoint (ULift.{u} ℂ)} :
    saDown x ≤ saDown y ↔ x ≤ y := Iff.rfl

private theorem saDown_saUp (c : selfAdjoint ℂ) : saDown (saUp.{u} c) = c := rfl

private theorem isLUB_saDown {D : Set (selfAdjoint (ULift.{u} ℂ))}
    {s : selfAdjoint (ULift.{u} ℂ)} (h : IsLUB D s) :
    IsLUB (saDown '' D) (saDown s) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact saDown_le_iff.mpr (h.1 hd)
  · intro c hc
    have hub : saUp.{u} c ∈ upperBounds D := by
      intro d hd
      have h1 : saDown d ≤ saDown (saUp.{u} c) := hc ⟨d, hd, rfl⟩
      exact saDown_le_iff.mp h1
    have h2 : saDown s ≤ saDown (saUp.{u} c) := saDown_le_iff.mpr (h.2 hub)
    exact h2

private theorem directedOn_saDown {D : Set (selfAdjoint (ULift.{u} ℂ))}
    (h : DirectedOn (· ≤ ·) D) : DirectedOn (· ≤ ·) (saDown '' D) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
  obtain ⟨z, hz, hdz, hez⟩ := h d hd e he
  exact ⟨saDown z, ⟨z, hz, rfl⟩, saDown_le_iff.mpr hdz, saDown_le_iff.mpr hez⟩

end ScalarsVNA

end

section

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A supremum of a nonempty set of self-adjoint elements taken in the
self-adjoint part is a supremum in the algebra: an upper bound of a nonempty
set of self-adjoint elements is itself self-adjoint. -/
theorem isLUB_coe_of_isLUB {D : Set (selfAdjoint A)} {s : selfAdjoint A}
    (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB ((fun d : selfAdjoint A => (d : A)) '' D) (s : A) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · intro c hc
    obtain ⟨d, hd⟩ := hne
    have hdc : (d : A) ≤ c := hc ⟨d, hd, rfl⟩
    have hsa : IsSelfAdjoint c := by
      have h0 : (0 : A) ≤ c - d := sub_nonneg.mpr hdc
      simpa using h0.isSelfAdjoint.add d.2
    have hub : (⟨c, hsa⟩ : selfAdjoint A) ∈ upperBounds D := by
      intro e he
      have h1 : (e : A) ≤ ((⟨c, hsa⟩ : selfAdjoint A) : A) := hc ⟨e, he, rfl⟩
      exact Subtype.coe_le_coe.mp h1
    exact Subtype.coe_le_coe.mpr (h.2 hub)

/-- A normal map is monotone on the self-adjoint part (apply normality to the
two-element set `{d, z}`). -/
theorem mono_of_preservesDirSups {f : A → B} (hf : Theses.PreservesDirSups f)
    {d z : selfAdjoint A} (h : d ≤ z) : f d ≤ f z := by
  have hlub : IsLUB ({d, z} : Set (selfAdjoint A)) z := by
    constructor
    · intro x hx
      rcases hx with rfl | hx
      · exact h
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact le_refl _
    · intro c hc
      exact hc (Or.inr rfl)
  have hdir : DirectedOn (· ≤ ·) ({d, z} : Set (selfAdjoint A)) := by
    intro x hx y hy
    refine ⟨z, Or.inr rfl, ?_, ?_⟩
    · rcases hx with rfl | hx
      · exact h
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact le_refl _
    · rcases hy with rfl | hy
      · exact h
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact le_refl _
  exact (hf _ z ⟨d, Or.inl rfl⟩ hdir hlub).1 ⟨d, Or.inl rfl, rfl⟩

/-- Normality is preserved by pointwise addition. -/
theorem preservesDirSups_add {f g : A → B} (hf : Theses.PreservesDirSups f)
    (hg : Theses.PreservesDirSups g) :
    Theses.PreservesDirSups (fun a => f a + g a) := by
  intro D s hne hdir hlub
  have hf' := hf D s hne hdir hlub
  have hg' := hg D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact add_le_add (hf'.1 ⟨d, hd, rfl⟩) (hg'.1 ⟨d, hd, rfl⟩)
  · intro c hc
    have step : ∀ e ∈ D, f s + g e ≤ c := by
      intro e he
      have hub : c - g e ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        obtain ⟨z, hz, hdz, hez⟩ := hdir d hd e he
        have h1 : f d + g e ≤ f z + g z :=
          add_le_add (mono_of_preservesDirSups hf hdz) (mono_of_preservesDirSups hg hez)
        exact le_sub_iff_add_le.mpr (h1.trans (hc ⟨z, hz, rfl⟩))
      exact add_le_of_le_sub_right (hf'.2 hub)
    have hub2 : c - f s ∈ upperBounds ((fun d : selfAdjoint A => g d) '' D) := by
      rintro _ ⟨e, he, rfl⟩
      have h2 := step e he
      rw [add_comm] at h2
      exact le_sub_iff_add_le.mpr h2
    have h3 := hg'.2 hub2
    rw [le_sub_iff_add_le, add_comm] at h3
    exact h3

end

section

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-! ### Complete positivity of the maps built from products -/

theorem sa_of_cp {f : A →ₗ[ℂ] B} (hf : IsCompletelyPositiveMap f) {a : A}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (f a) := by
  have hi := cstar_p_implies_i f (astara_pos_basic_2_cp f hf)
  have := hi a
  rw [ha] at this
  exact this.symm

theorem cp_add {f g : A →ₗ[ℂ] B} (hf : IsCompletelyPositiveMap f)
    (hg : IsCompletelyPositiveMap g) : IsCompletelyPositiveMap (f + g) := by
  intro n a b
  have hrw : ∀ i j : Fin n, star (b i) * (f + g) (star (a i) * a j) * b j
      = star (b i) * f (star (a i) * a j) * b j
        + star (b i) * g (star (a i) * a j) * b j := by
    intro i j
    simp [mul_add, add_mul]
  simp_rw [hrw, Finset.sum_add_distrib]
  exact add_nonneg (hf n a b) (hg n a b)

theorem cp_prod {f : C →ₗ[ℂ] A} {g : C →ₗ[ℂ] B} (hf : IsCompletelyPositiveMap f)
    (hg : IsCompletelyPositiveMap g) :
    IsCompletelyPositiveMap (LinearMap.prod f g) := by
  intro n a b
  refine Prod.le_def.mpr ⟨?_, ?_⟩
  · have h : (∑ i, ∑ j, star (b i) * (LinearMap.prod f g) (star (a i) * a j) * b j).1
        = ∑ i, ∑ j, star (b i).1 * f (star (a i) * a j) * (b j).1 := by
      simp [Prod.fst_sum]
    rw [show (0 : A × B).1 = 0 from rfl, h]
    exact hf n a (fun i => (b i).1)
  · have h : (∑ i, ∑ j, star (b i) * (LinearMap.prod f g) (star (a i) * a j) * b j).2
        = ∑ i, ∑ j, star (b i).2 * g (star (a i) * a j) * (b j).2 := by
      simp [Prod.snd_sum]
    rw [show (0 : A × B).2 = 0 from rfl, h]
    exact hg n a (fun i => (b i).2)

theorem cp_fstLin : IsCompletelyPositiveMap (LinearMap.fst ℂ A B) :=
  cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl)

theorem cp_sndLin : IsCompletelyPositiveMap (LinearMap.snd ℂ A B) :=
  cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl)

theorem cp_inlLin : IsCompletelyPositiveMap (LinearMap.inl ℂ A B) :=
  cp_of_mi _ (fun _ _ => Prod.ext rfl (by simp)) (fun _ => Prod.ext rfl (by simp))

theorem cp_inrLin : IsCompletelyPositiveMap (LinearMap.inr ℂ A B) :=
  cp_of_mi _ (fun _ _ => Prod.ext (by simp) rfl) (fun _ => Prod.ext (by simp) rfl)

/-! ### Normality of the maps built from products -/

theorem preservesDirSups_fstFun :
    Theses.PreservesDirSups (fun x : A × B => x.1) := by
  intro D s hne hdir hlub
  have h := isLUB_coe_of_isLUB (A := A) (hne.image _) (isLUB_saFst hlub)
  rwa [Set.image_image] at h

theorem preservesDirSups_sndFun :
    Theses.PreservesDirSups (fun x : A × B => x.2) := by
  intro D s hne hdir hlub
  have h := isLUB_coe_of_isLUB (A := B) (hne.image _) (isLUB_saSnd hlub)
  rwa [Set.image_image] at h

theorem preservesDirSups_prodFun {f : A → B} {g : A → C}
    (hf : Theses.PreservesDirSups f) (hg : Theses.PreservesDirSups g) :
    Theses.PreservesDirSups (fun a => (f a, g a)) := by
  intro D s hne hdir hlub
  have hf' := hf D s hne hdir hlub
  have hg' := hg D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Prod.le_def.mpr ⟨hf'.1 ⟨d, hd, rfl⟩, hg'.1 ⟨d, hd, rfl⟩⟩
  · intro c hc
    refine Prod.le_def.mpr ⟨hf'.2 ?_, hg'.2 ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact (Prod.le_def.mp (hc ⟨d, hd, rfl⟩)).1
    · rintro _ ⟨d, hd, rfl⟩
      exact (Prod.le_def.mp (hc ⟨d, hd, rfl⟩)).2

theorem preservesDirSups_inlFun :
    Theses.PreservesDirSups (fun a : A => ((a, 0) : A × B)) := by
  intro D s hne hdir hlub
  have h := isLUB_coe_of_isLUB hne hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Prod.le_def.mpr ⟨h.1 ⟨d, hd, rfl⟩, le_refl _⟩
  · intro c hc
    obtain ⟨d₀, hd₀⟩ := hne
    refine Prod.le_def.mpr ⟨h.2 ?_, (Prod.le_def.mp (hc ⟨d₀, hd₀, rfl⟩)).2⟩
    rintro _ ⟨d, hd, rfl⟩
    exact (Prod.le_def.mp (hc ⟨d, hd, rfl⟩)).1

theorem preservesDirSups_inrFun :
    Theses.PreservesDirSups (fun b : B => ((0, b) : A × B)) := by
  intro D s hne hdir hlub
  have h := isLUB_coe_of_isLUB hne hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Prod.le_def.mpr ⟨le_refl _, h.1 ⟨d, hd, rfl⟩⟩
  · intro c hc
    obtain ⟨d₀, hd₀⟩ := hne
    refine Prod.le_def.mpr ⟨(Prod.le_def.mp (hc ⟨d₀, hd₀, rfl⟩)).1, h.2 ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact (Prod.le_def.mp (hc ⟨d, hd, rfl⟩)).2

/-- Normality of a composite `g ∘ f`, where `f` is normal and preserves
self-adjointness. -/
theorem preservesDirSups_comp' {f : A → B} {g : B → C}
    (hf : Theses.PreservesDirSups f) (hfsa : ∀ a : selfAdjoint A, IsSelfAdjoint (f a))
    (hg : Theses.PreservesDirSups g) :
    Theses.PreservesDirSups (fun a => g (f a)) := by
  intro D s hne hdir hlub
  have hfD := hf D s hne hdir hlub
  let F : selfAdjoint A → selfAdjoint B := fun a => ⟨f a, hfsa a⟩
  have hne' : (F '' D).Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) (F '' D) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    obtain ⟨z, hz, hdz, hez⟩ := hdir d hd e he
    refine ⟨F z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (mono_of_preservesDirSups hf hdz)
    · exact Subtype.coe_le_coe.mp (mono_of_preservesDirSups hf hez)
  have hlub' : IsLUB (F '' D) (F s) := by
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mp (hfD.1 ⟨d, hd, rfl⟩)
    · intro b hb
      have hbb : (b : B) ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        exact Subtype.coe_le_coe.mpr (hb ⟨d, hd, rfl⟩)
      exact Subtype.coe_le_coe.mp (hfD.2 hbb)
  have h := hg _ (F s) hne' hdir' hlub'
  rwa [Set.image_image] at h

end

section

/-! ### `ℂᵤ` is a von Neumann algebra -/

private noncomputable def cuDownLin : ULift.{u} ℂ →ₗ[ℂ] ℂ where
  toFun := ULift.down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def npDown : Theses.NPFunctional (ULift.{u} ℂ) where
  toPositiveLinearMap := { toLinearMap := cuDownLin, monotone' := fun _ _ h => h }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := isLUB_coe_of_isLUB (A := ℂ) (hne.image _) (isLUB_saDown hlub)
    rwa [Set.image_image] at h

/-- **The scalars `ℂᵤ` form a von Neumann algebra** (transported from `ℂ`
along `ULift.down`, which is an order isomorphism on self-adjoint parts). -/
instance instVonNeumannAlgebraCU : Theses.VonNeumannAlgebra (ULift.{u} ℂ) where
  isLUB_of_bddAbove_directed D hne hdir hbdd := by
    obtain ⟨c, hc⟩ := hbdd
    obtain ⟨s, hs⟩ := Theses.VonNeumannAlgebra.isLUB_of_bddAbove_directed
      (saDown '' D) (hne.image _) (directedOn_saDown hdir)
      ⟨saDown c, by rintro _ ⟨d, hd, rfl⟩; exact saDown_le_iff.mpr (hc hd)⟩
    refine ⟨saUp s, ?_, ?_⟩
    · intro d hd
      have h1 : saDown d ≤ saDown (saUp.{u} s) := hs.1 ⟨d, hd, rfl⟩
      exact saDown_le_iff.mp h1
    · intro x hx
      have hub : saDown x ∈ upperBounds (saDown '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        exact saDown_le_iff.mpr (hx hd)
      have h2 : saDown (saUp.{u} s) ≤ saDown x := hs.2 hub
      exact saDown_le_iff.mp h2
  np_faithful a ha h := by
    have h0 : a.down = 0 := h npDown
    cases a
    exact congrArg ULift.up h0

end

section

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-! ### Building ncp-, ncpu- and ncpsu-maps -/

/-- The underlying linear map of an ncp-map. -/
noncomputable def ncpLin (f : Theses.NCPMap A B) : A →ₗ[ℂ] B :=
  f.toCompletelyPositiveMap.toLinearMap

@[simp] theorem ncpLin_apply (f : Theses.NCPMap A B) (a : A) : ncpLin f a = f a := rfl

theorem ncpLin_cp (f : Theses.NCPMap A B) : IsCompletelyPositiveMap (ncpLin f) :=
  (cp_iff (ncpLin f)).out 1 0 |>.mp
    (fun N M hM => f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM)

theorem ncpLin_normal (f : Theses.NCPMap A B) :
    Theses.PreservesDirSups ⇑(ncpLin f) := f.preservesDirSups'

/-- An ncp-map from a linear map that is completely positive and normal. -/
noncomputable def mkNCP (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) : Theses.NCPMap A B where
  toCompletelyPositiveMap :=
    { toLinearMap := f
      map_cstarMatrix_nonneg' := (cp_iff f).out 0 1 |>.mp hcp }
  preservesDirSups' := hn

@[simp] theorem mkNCP_apply (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) (a : A) : mkNCP f hcp hn a = f a := rfl

/-- An ncpu-map from a linear map. -/
noncomputable def mkNCPU (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) (hu : f 1 = 1) : Theses.NCPUMap A B :=
  ⟨mkNCP f hcp hn, hu⟩

@[simp] theorem mkNCPU_apply (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) (hu : f 1 = 1) (a : A) :
    (mkNCPU f hcp hn hu).toNCPMap a = f a := rfl

/-- Extensionality for ncpu-maps. -/
theorem ncpu_ext {f g : Theses.NCPUMap A B}
    (h : ∀ a, f.toNCPMap a = g.toNCPMap a) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hfg : f = g := DFunLike.coe_injective (funext h)
  subst hfg
  rfl

/-! ### The concrete ncpu-maps of the presentation -/

/-- The first projection `A × B → A`. -/
noncomputable def wFst (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Theses.NCPUMap (A × B) A :=
  mkNCPU (LinearMap.fst ℂ A B) cp_fstLin preservesDirSups_fstFun rfl

/-- The second projection `A × B → B`. -/
noncomputable def wSnd (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Theses.NCPUMap (A × B) B :=
  mkNCPU (LinearMap.snd ℂ A B) cp_sndLin preservesDirSups_sndFun rfl

@[simp] theorem wFst_apply (x : A × B) : (wFst A B).toNCPMap x = x.1 := rfl
@[simp] theorem wSnd_apply (x : A × B) : (wSnd A B).toNCPMap x = x.2 := rfl

/-- The pairing `⟨f, g⟩ : C → A × B` of two ncpu-maps. -/
noncomputable def wPair (f : Theses.NCPUMap C A) (g : Theses.NCPUMap C B) :
    Theses.NCPUMap C (A × B) :=
  mkNCPU (LinearMap.prod (ncpLin f.toNCPMap) (ncpLin g.toNCPMap))
    (cp_prod (ncpLin_cp _) (ncpLin_cp _))
    (preservesDirSups_prodFun (ncpLin_normal f.toNCPMap) (ncpLin_normal g.toNCPMap))
    (Prod.ext f.unital' g.unital')

@[simp] theorem wPair_apply (f : Theses.NCPUMap C A) (g : Theses.NCPUMap C B) (c : C) :
    (wPair f g).toNCPMap c = (f.toNCPMap c, g.toNCPMap c) := rfl

/-- The unique ncpu-map `ℂᵤ → A`, `z ↦ z·1`. -/
noncomputable def wUnit (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPUMap (ULift.{u} ℂ) A :=
  ⟨Theses.A.VN.ncpOfNonneg (zero_le_one' A), by
    show (1 : ULift.{u} ℂ).down • (1 : A) = 1
    simp⟩

@[simp] theorem wUnit_apply (z : ULift.{u} ℂ) :
    (wUnit A).toNCPMap z = z.down • (1 : A) := rfl

/-! ### **98X**: a faithful unital ncp-map need not be an isomorphism

The Example's second sentence (proc.tex:733).  It cannot be stated in
`A/Proc` — there is no von Neumann structure on `ℂ²` upstream of
`Measurement.lean`; both `instVonNeumannAlgebraProd` and
`instVonNeumannAlgebraCU` are here — so it is stated here, at the first
point where its witness exists. -/

/-- Normality is preserved by a positive real scalar multiple.  The `½` of
98X's witness needs this, and `preservesDirSups_add` alone does not give it. -/
theorem preservesDirSups_ofReal_smul {f : A → B} (hf : Theses.PreservesDirSups f)
    {r : ℝ} (hr : 0 < r) :
    Theses.PreservesDirSups (fun a => ((r : ℝ) : ℂ) • f a) := by
  have hmono : ∀ t : ℝ, 0 ≤ t → ∀ {x y : B}, x ≤ y →
      ((t : ℝ) : ℂ) • x ≤ ((t : ℝ) : ℂ) • y := by
    intro t ht x y h
    have := ofReal_smul_nonneg (sub_nonneg.mpr h) ht
    rwa [smul_sub, sub_nonneg] at this
  intro D s hne hdir hlub
  have h := hf D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact hmono r hr.le (h.1 ⟨d, hd, rfl⟩)
  · intro c hc
    have hub : ((r⁻¹ : ℝ) : ℂ) • c ∈ upperBounds ((fun d : selfAdjoint A => f d) '' D) := by
      rintro _ ⟨d, hd, rfl⟩
      have hstep := hmono r⁻¹ (inv_pos.mpr hr).le (hc ⟨d, hd, rfl⟩)
      rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one,
        one_smul] at hstep
    have hstep := hmono r hr.le (h.2 hub)
    rwa [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul] at hstep

/-- 98X's witness `(λ, μ) ↦ ½(λ + μ)`, as a `ℂ`-linear map. -/
noncomputable def avgLin : (ULift.{u} ℂ × ULift.{u} ℂ) →ₗ[ℂ] ULift.{u} ℂ :=
  (2⁻¹ : ℂ) • (LinearMap.fst ℂ (ULift.{u} ℂ) (ULift.{u} ℂ)
    + LinearMap.snd ℂ (ULift.{u} ℂ) (ULift.{u} ℂ))

theorem avgLin_apply (x : ULift.{u} ℂ × ULift.{u} ℂ) :
    avgLin x = (2⁻¹ : ℂ) • (x.1 + x.2) := rfl

theorem avgLin_positive : IsPositiveMap (avgLin.{u}) := by
  intro a ha
  obtain ⟨h1, h2⟩ := Prod.le_def.mp ha
  rw [avgLin_apply]
  have hsum : (0 : ULift.{u} ℂ) ≤ a.1 + a.2 := add_nonneg h1 h2
  have h : ((2⁻¹ : ℝ) : ℂ) • (a.1 + a.2) = (2⁻¹ : ℂ) • (a.1 + a.2) := by norm_num
  rw [← h]
  exact ofReal_smul_nonneg hsum (by norm_num)

/-- Complete positivity, from **34IX**.2 `cp_commutative_dom`: the domain
`ℂ²` is commutative, so positivity is enough. -/
theorem avgLin_cp : IsCompletelyPositiveMap (avgLin.{u}) := by
  letI : CommCStarAlgebra (ULift.{u} ℂ × ULift.{u} ℂ) :=
    { mul_comm := fun a b => by
        refine Prod.ext ?_ ?_ <;> · apply ULift.ext; simp [mul_comm] }
  exact cp_commutative_dom _ avgLin_positive

theorem avgLin_normal : Theses.PreservesDirSups (avgLin.{u}) := by
  have hadd : Theses.PreservesDirSups
      (fun x : ULift.{u} ℂ × ULift.{u} ℂ => x.1 + x.2) :=
    preservesDirSups_add preservesDirSups_fstFun preservesDirSups_sndFun
  have h := preservesDirSups_ofReal_smul hadd (r := (2⁻¹ : ℝ)) (by norm_num)
  have hfun : (fun x : ULift.{u} ℂ × ULift.{u} ℂ => (((2⁻¹ : ℝ) : ℂ) • (x.1 + x.2)))
      = ⇑(avgLin.{u}) := by
    funext x; rw [avgLin_apply]; norm_num
  rwa [hfun] at h

/-- 98X's witness as an ncp-map. -/
noncomputable def avgNCP : Theses.NCPMap (ULift.{u} ℂ × ULift.{u} ℂ) (ULift.{u} ℂ) :=
  mkNCP avgLin.{u} avgLin_cp avgLin_normal

@[simp] theorem avgNCP_apply (x : ULift.{u} ℂ × ULift.{u} ℂ) :
    avgNCP.{u} x = (2⁻¹ : ℂ) • (x.1 + x.2) := rfl

theorem avgNCP_unital : avgNCP.{u} 1 = 1 := by
  rw [avgNCP_apply]
  apply ULift.ext
  show (2⁻¹ : ℂ) * ((1 : ℂ) + 1) = 1
  norm_num

theorem avgNCP_not_injective : ¬ Function.Injective ⇑(avgNCP.{u}) := by
  intro hinj
  have h : avgNCP.{u} (ULift.up 1, ULift.up (-1)) = avgNCP.{u} 0 := by
    rw [avgNCP_apply, avgNCP_apply]
    apply ULift.ext
    show (2⁻¹ : ℂ) * ((1 : ℂ) + -1) = (2⁻¹ : ℂ) * ((0 : ℂ) + 0)
    norm_num
  have h1 : (ULift.up (1 : ℂ) : ULift.{u} ℂ) = ULift.up 0 := congrArg Prod.fst (hinj h)
  exact one_ne_zero (ULift.up.inj h1)

theorem avgNCP_faithful {x : ULift.{u} ℂ × ULift.{u} ℂ} (hx : 0 ≤ x)
    (h : avgNCP.{u} x = 0) : x = 0 := by
  obtain ⟨h1, h2⟩ := Prod.le_def.mp hx
  have h1' : (0 : ℂ) ≤ x.1.down := h1
  have h2' : (0 : ℂ) ≤ x.2.down := h2
  have hd : (2⁻¹ : ℂ) * (x.1.down + x.2.down) = 0 := by
    have hdown := congrArg ULift.down h
    rw [avgNCP_apply] at hdown
    exact hdown
  have hsum : x.1.down + x.2.down = 0 := by
    rcases mul_eq_zero.mp hd with h0 | h0
    · exact absurd h0 (by norm_num)
    · exact h0
  obtain ⟨hr1, hi1⟩ := Complex.nonneg_iff.mp h1'
  obtain ⟨hr2, hi2⟩ := Complex.nonneg_iff.mp h2'
  have hre : x.1.down.re + x.2.down.re = 0 := by
    have := congrArg Complex.re hsum; simpa using this
  have e1 : x.1.down.re = 0 := le_antisymm (by linarith) hr1
  have e2 : x.2.down.re = 0 := le_antisymm (by linarith) hr2
  refine Prod.ext ?_ ?_ <;> apply ULift.ext <;> apply Complex.ext
  · exact e1
  · exact hi1.symm
  · exact e2
  · exact hi2.symm

theorem avgNCP_carrier : Theses.A.Proc.ncpCarrier avgNCP.{u} = 1 := by
  have hP1 : IsStarProjection (1 : ULift.{u} ℂ × ULift.{u} ℂ) ∧
      avgNCP.{u} (1 - 1) = 0 ∧
      ∀ q : ULift.{u} ℂ × ULift.{u} ℂ, IsStarProjection q →
        avgNCP.{u} (1 - q) = 0 → (1 : ULift.{u} ℂ × ULift.{u} ℂ) ≤ q := by
    refine ⟨IsStarProjection.one _, ?_, ?_⟩
    · rw [sub_self, avgNCP_apply]
      apply ULift.ext
      show (2⁻¹ : ℂ) * ((0 : ℂ) + 0) = 0
      norm_num
    · intro q hq hfq
      have hq1 : (0 : ULift.{u} ℂ × ULift.{u} ℂ) ≤ 1 - q := sub_nonneg.mpr hq.le_one
      have hq' : q = 1 := (sub_eq_zero.mp (avgNCP_faithful hq1 hfq)).symm
      rw [hq']
  exact (Theses.A.Proc.exists_ncpCarrier avgNCP.{u}).unique
    (Theses.A.Proc.exists_ncpCarrier avgNCP.{u}).choose_spec.1 hP1

/-- **98X** (proc.tex:733, Example), second sentence: a **faithful unital
ncp-map need not be an isomorphism**.  The witness is the thesis's own,
`f : ℂ² → ℂ`, `(λ, μ) ↦ ½(λ + μ)`: unital, with carrier `1` (faithful), and
not injective, since it kills `(1, −1)`. -/
theorem exists_faithful_unital_ncp_not_bijective :
    ∃ f : Theses.NCPMap (ULift.{u} ℂ × ULift.{u} ℂ) (ULift.{u} ℂ),
      f 1 = 1 ∧ Theses.A.Proc.ncpCarrier f = 1 ∧ ¬ Function.Bijective ⇑f :=
  ⟨avgNCP.{u}, avgNCP_unital, avgNCP_carrier, fun h => avgNCP_not_injective h.1⟩


end

section

/-! ### The category `vN` -/

theorem vn_hom_ext {X Y : WStarNCPU.{u}} {f g : X ⟶ Y}
    (h : ∀ a, f.toNCPMap a = g.toNCPMap a) : f = g := ncpu_ext h

theorem vn_comp_apply {X Y Z : WStarNCPU.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X.base) :
    (f ≫ g).toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  (NCPUMap.exists_comp f g).choose_spec a

theorem vn_id_apply {X : WStarNCPU.{u}} (a : X.base) :
    (𝟙 X : Theses.NCPUMap X.base.carrier X.base.carrier).toNCPMap a = a :=
  (NCPUMap.exists_id X.base.carrier).choose_spec a

theorem vnop_hom_ext {X Y : WStarNCPU.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ a, f.unop.toNCPMap a = g.unop.toNCPMap a) : f = g :=
  Quiver.Hom.unop_inj (vn_hom_ext h)

theorem vnop_comp_apply {X Y Z : WStarNCPU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Z.unop.base) :
    (f ≫ g).unop.toNCPMap a = f.unop.toNCPMap (g.unop.toNCPMap a) :=
  vn_comp_apply g.unop f.unop a

theorem vnop_congr {X Y : WStarNCPU.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (a : Y.unop.base) : f.unop.toNCPMap a = g.unop.toNCPMap a := by rw [h]

/-- Postcomposition with a fixed map, pointwise. -/
theorem vnop_comp_congr {Z P X : WStarNCPU.{u}ᵒᵖ} {F : P ⟶ X} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : X.unop.base) :
    a.unop.toNCPMap (F.unop.toNCPMap x) = b.unop.toNCPMap (F.unop.toNCPMap x) :=
  ((vnop_comp_apply a F x).symm.trans (vnop_congr h x)).trans
    (vnop_comp_apply b F x)

/-! ### `ℂᵤ` is initial and the trivial algebra is final -/

theorem wUnit_unique {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (f : Theses.NCPUMap (ULift.{u} ℂ) A) : f = wUnit A := by
  refine ncpu_ext fun z => ?_
  have hz : (z.down • (1 : ULift.{u} ℂ)) = z :=
    Theses.A.VN.CU.down_injective (by simp)
  have hlin : f.toNCPMap (z.down • (1 : ULift.{u} ℂ)) = z.down • f.toNCPMap 1 :=
    map_smul (ncpLin f.toNCPMap) z.down 1
  rw [wUnit_apply]
  conv_lhs => rw [← hz]
  rw [hlin, f.unital']

/-- **`ℂᵤ` is the initial object of `vN`** (the unique ncpu-map `ℂᵤ → A` is
`z ↦ z·1`), hence the final object of `vNᵒᵖ`. -/
noncomputable def vnScalIsInitial :
    IsInitial (WStarNCPU.of (WStar.of (ULift.{u} ℂ))) :=
  IsInitial.ofUniqueHom (fun X => wUnit X.base.carrier)
    (fun _ f => wUnit_unique f)

/-- The unique ncpu-map into the trivial algebra. -/
noncomputable def wTriv (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPUMap A PUnit.{u + 1} :=
  mkNCPU 0 (fun _ _ _ => le_of_eq (Subsingleton.elim _ _))
    (fun _ _ _ _ _ => ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
      fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩)
    (Subsingleton.elim _ _)

/-- **The trivial algebra is the final object of `vN`**, hence the initial
object of `vNᵒᵖ`. -/
noncomputable def vnTrivIsTerminal :
    IsTerminal (WStarNCPU.of (WStar.of PUnit.{u + 1})) :=
  IsTerminal.ofUniqueHom (fun X => wTriv X.base.carrier)
    (fun _ _ => ncpu_ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-! ### The concrete presentation of `vNᵒᵖ` -/

/-- The concrete presentation of `vNᵒᵖ`: the final object is the scalars
`ℂᵤ` (initial in `vN`), the binary coproducts are the products `A × B`. -/
noncomputable def vnPres : CoprodPres (WStarNCPU.{u}ᵒᵖ) where
  T := Opposite.op (WStarNCPU.of (WStar.of (ULift.{u} ℂ)))
  hT := IsInitial.op (WStarNCPU.{u}) vnScalIsInitial
  P X Y := Opposite.op (WStarNCPU.of (WStar.of
    (X.unop.base.carrier × Y.unop.base.carrier)))
  pinl X Y := Quiver.Hom.op (wFst X.unop.base.carrier Y.unop.base.carrier)
  pinr X Y := Quiver.Hom.op (wSnd X.unop.base.carrier Y.unop.base.carrier)
  hP X Y := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op (wPair u.unop v.unop))
    (fun {_} u v => vnop_hom_ext fun a => vnop_comp_apply _ _ a)
    (fun {_} u v => vnop_hom_ext fun a => vnop_comp_apply _ _ a)
    (fun {W} u v m h₁ h₂ => vnop_hom_ext fun a => by
      refine Prod.ext ?_ ?_
      · exact (vnop_comp_apply _ m a).symm.trans (vnop_congr h₁ a)
      · exact (vnop_comp_apply _ m a).symm.trans (vnop_congr h₂ a))

end

section

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A linear map between C\*-algebras vanishing on the positive cone is zero
(every element is a linear combination of four positive elements). -/
theorem linear_eq_zero_of_nonneg {f : A →ₗ[ℂ] C}
    (h : ∀ a : A, 0 ≤ a → f a = 0) (x : A) : f x = 0 := by
  have hsa : ∀ a : A, IsSelfAdjoint a → f a = 0 := by
    intro a ha
    rw [← CFC.posPart_sub_negPart a ha, map_sub, h _ (CFC.posPart_nonneg a),
      h _ (CFC.negPart_nonneg a), sub_zero]
  have hx := realPart_add_I_smul_imaginaryPart x
  rw [← hx, map_add, map_smul, hsa _ (ℜ x).2, hsa _ (ℑ x).2, smul_zero, add_zero]

/-- The identity ncpu-map (built directly, not through `Classical.choice`). -/
noncomputable def idMap (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPUMap A A :=
  mkNCPU LinearMap.id (cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl))
    (fun _ _ hne _ hlub => isLUB_coe_of_isLUB hne hlub) rfl

@[simp] theorem idMap_apply (a : A) : (idMap A).toNCPMap a = a := rfl

/-- The product `f × g : A × B → A' × B'` of two ncpu-maps. -/
noncomputable def wProdMap {A' B' : Type u} [CStarAlgebra A'] [PartialOrder A']
    [StarOrderedRing A'] [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    (f : Theses.NCPUMap A A') (g : Theses.NCPUMap B B') :
    Theses.NCPUMap (A × B) (A' × B') :=
  mkNCPU (LinearMap.prodMap (ncpLin f.toNCPMap) (ncpLin g.toNCPMap))
    (cp_prod (cp_comp _ _ cp_fstLin (ncpLin_cp _))
      (cp_comp _ _ cp_sndLin (ncpLin_cp _)))
    (preservesDirSups_prodFun
      (preservesDirSups_comp' (f := fun x : A × B => x.1)
        (g := ⇑(ncpLin f.toNCPMap)) preservesDirSups_fstFun
        (fun a => prod_sa_fst a.2) (ncpLin_normal _))
      (preservesDirSups_comp' (f := fun x : A × B => x.2)
        (g := ⇑(ncpLin g.toNCPMap)) preservesDirSups_sndFun
        (fun a => prod_sa_snd a.2) (ncpLin_normal _)))
    (Prod.ext f.unital' g.unital')

@[simp] theorem wProdMap_apply {A' B' : Type u} [CStarAlgebra A'] [PartialOrder A']
    [StarOrderedRing A'] [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    (f : Theses.NCPUMap A A') (g : Theses.NCPUMap B B') (x : A × B) :
    (wProdMap f g).toNCPMap x = (f.toNCPMap x.1, g.toNCPMap x.2) := rfl

end

section

/-- Two equal ncpu-maps agree pointwise. -/
theorem vn_congr {X Y : WStarNCPU.{u}} {f g : X ⟶ Y} (h : f = g) (a : X.base) :
    f.toNCPMap a = g.toNCPMap a := by rw [h]

/-- An algebra as an object of `vN`. -/
noncomputable abbrev OB (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] : WStarNCPU.{u} :=
  WStarNCPU.of (WStar.of A)

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem sa_prod {x : A} {y : B} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    IsSelfAdjoint ((x, y) : A × B) := by
  show star ((x, y) : A × B) = (x, y)
  exact Prod.ext hx hy

/-- The mediating ncpu-map `γ(a, b) = β(a, 0) + α(0, b)` of the first
pushout square of 180I. -/
noncomputable def med1 (α : Theses.NCPUMap (ULift.{u} ℂ × B) C)
    (β : Theses.NCPUMap (A × ULift.{u} ℂ) C)
    (hc : ∀ z w : ULift.{u} ℂ,
      α.toNCPMap (z, w.down • (1 : B)) = β.toNCPMap (z.down • (1 : A), w)) :
    Theses.NCPUMap (A × B) C :=
  mkNCPU ((ncpLin β.toNCPMap).comp
        ((LinearMap.inl ℂ A (ULift.{u} ℂ)).comp (LinearMap.fst ℂ A B))
      + (ncpLin α.toNCPMap).comp
        ((LinearMap.inr ℂ (ULift.{u} ℂ) B).comp (LinearMap.snd ℂ A B)))
    (cp_add (cp_comp _ _ (cp_comp _ _ cp_fstLin cp_inlLin) (ncpLin_cp _))
      (cp_comp _ _ (cp_comp _ _ cp_sndLin cp_inrLin) (ncpLin_cp _)))
    (preservesDirSups_add
      (preservesDirSups_comp'
        (f := fun x : A × B => ((x.1, 0) : A × ULift.{u} ℂ))
        (g := ⇑(ncpLin β.toNCPMap))
        (preservesDirSups_comp' (f := fun x : A × B => x.1)
          (g := fun a : A => ((a, 0) : A × ULift.{u} ℂ))
          preservesDirSups_fstFun (fun a => prod_sa_fst a.2) preservesDirSups_inlFun)
        (fun a => sa_prod (prod_sa_fst a.2) (star_zero _)) (ncpLin_normal _))
      (preservesDirSups_comp'
        (f := fun x : A × B => ((0, x.2) : ULift.{u} ℂ × B))
        (g := ⇑(ncpLin α.toNCPMap))
        (preservesDirSups_comp' (f := fun x : A × B => x.2)
          (g := fun b : B => ((0, b) : ULift.{u} ℂ × B))
          preservesDirSups_sndFun (fun a => prod_sa_snd a.2) preservesDirSups_inrFun)
        (fun a => sa_prod (star_zero _) (prod_sa_snd a.2)) (ncpLin_normal _)))
    (by
      have h1 : α.toNCPMap ((1 : ULift.{u} ℂ), (0 : B))
          = β.toNCPMap ((1 : A), (0 : ULift.{u} ℂ)) := by
        have h := hc 1 0
        simpa using h
      show β.toNCPMap ((1 : A), (0 : ULift.{u} ℂ))
        + α.toNCPMap ((0 : ULift.{u} ℂ), (1 : B)) = 1
      rw [← h1]
      have h2 : ((1 : ULift.{u} ℂ), (0 : B)) + ((0 : ULift.{u} ℂ), (1 : B))
          = (1 : ULift.{u} ℂ × B) := by
        refine Prod.ext ?_ ?_ <;> simp
      have h3 := map_add (ncpLin α.toNCPMap) ((1 : ULift.{u} ℂ), (0 : B))
        ((0 : ULift.{u} ℂ), (1 : B))
      rw [h2] at h3
      exact h3.symm.trans α.unital')

@[simp] theorem med1_apply (α : Theses.NCPUMap (ULift.{u} ℂ × B) C)
    (β : Theses.NCPUMap (A × ULift.{u} ℂ) C) (hc) (x : A × B) :
    (med1 α β hc).toNCPMap x
      = β.toNCPMap (x.1, 0) + α.toNCPMap (0, x.2) := rfl

section Med1

variable (α : Theses.NCPUMap (ULift.{u} ℂ × B) C)
  (β : Theses.NCPUMap (A × ULift.{u} ℂ) C)
  (hc : ∀ z w : ULift.{u} ℂ,
    α.toNCPMap (z, w.down • (1 : B)) = β.toNCPMap (z.down • (1 : A), w))

/-- `γ ∘ (u × id) = α`. -/
theorem med1_fac_left (y : ULift.{u} ℂ × B) :
    (med1 α β hc).toNCPMap (y.1.down • (1 : A), y.2) = α.toNCPMap y := by
  show β.toNCPMap (y.1.down • (1 : A), 0) + α.toNCPMap (0, y.2) = α.toNCPMap y
  have h1 : α.toNCPMap (y.1, (0 : B))
      = β.toNCPMap (y.1.down • (1 : A), (0 : ULift.{u} ℂ)) := by
    have h := hc y.1 0
    simpa using h
  rw [← h1]
  have h2 := map_add (ncpLin α.toNCPMap)
    ((y.1, (0 : B)) : ULift.{u} ℂ × B) (((0 : ULift.{u} ℂ), y.2) : ULift.{u} ℂ × B)
  have h3 : ((y.1, (0 : B)) : ULift.{u} ℂ × B)
      + (((0 : ULift.{u} ℂ), y.2) : ULift.{u} ℂ × B) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h3] at h2
  exact h2.symm

/-- `γ ∘ (id × u) = β`. -/
theorem med1_fac_right (y : A × ULift.{u} ℂ) :
    (med1 α β hc).toNCPMap (y.1, y.2.down • (1 : B)) = β.toNCPMap y := by
  show β.toNCPMap (y.1, 0) + α.toNCPMap (0, y.2.down • (1 : B)) = β.toNCPMap y
  have h1 : α.toNCPMap ((0 : ULift.{u} ℂ), y.2.down • (1 : B))
      = β.toNCPMap ((0 : A), y.2) := by
    have h := hc 0 y.2
    simpa using h
  rw [h1]
  have h2 := map_add (ncpLin β.toNCPMap)
    ((y.1, (0 : ULift.{u} ℂ)) : A × ULift.{u} ℂ)
    (((0 : A), y.2) : A × ULift.{u} ℂ)
  have h3 : ((y.1, (0 : ULift.{u} ℂ)) : A × ULift.{u} ℂ)
      + (((0 : A), y.2) : A × ULift.{u} ℂ) = y := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h3] at h2
  exact h2.symm

/-- `γ` is the *only* map with those two properties. -/
theorem med1_uniq (m : Theses.NCPUMap (A × B) C)
    (h₁ : ∀ y : ULift.{u} ℂ × B,
      m.toNCPMap (y.1.down • (1 : A), y.2) = α.toNCPMap y)
    (h₂ : ∀ y : A × ULift.{u} ℂ,
      m.toNCPMap (y.1, y.2.down • (1 : B)) = β.toNCPMap y) :
    m = med1 α β hc := by
  refine ncpu_ext fun x => ?_
  show m.toNCPMap x = β.toNCPMap (x.1, 0) + α.toNCPMap (0, x.2)
  have e₁ : m.toNCPMap ((x.1, (0 : B)) : A × B) = β.toNCPMap (x.1, 0) := by
    have h := h₂ ((x.1, (0 : ULift.{u} ℂ)) : A × ULift.{u} ℂ)
    simpa using h
  have e₂ : m.toNCPMap (((0 : A), x.2) : A × B) = α.toNCPMap (0, x.2) := by
    have h := h₁ (((0 : ULift.{u} ℂ), x.2) : ULift.{u} ℂ × B)
    simpa using h
  have h2 := map_add (ncpLin m.toNCPMap) ((x.1, (0 : B)) : A × B)
    (((0 : A), x.2) : A × B)
  have h3 : ((x.1, (0 : B)) : A × B) + (((0 : A), x.2) : A × B) = x := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h3] at h2
  rw [show m.toNCPMap x = ncpLin m.toNCPMap x from rfl, h2]
  show m.toNCPMap ((x.1, (0 : B)) : A × B) + m.toNCPMap (((0 : A), x.2) : A × B) = _
  rw [e₁, e₂]

end Med1

end

section

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Theses.VonNeumannAlgebra A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B]

/-! ### The left pullback square of 180I -/

/-- `id × u : ℂ × ℂ ⟶ ℂ × B`. -/
noncomputable def sq1f (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    OB (ULift.{u} ℂ × ULift.{u} ℂ) ⟶ OB (ULift.{u} ℂ × B) :=
  wProdMap (idMap (ULift.{u} ℂ)) (wUnit B)

/-- `u × id : ℂ × ℂ ⟶ A × ℂ`. -/
noncomputable def sq1g (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    OB (ULift.{u} ℂ × ULift.{u} ℂ) ⟶ OB (A × ULift.{u} ℂ) :=
  wProdMap (wUnit A) (idMap (ULift.{u} ℂ))

/-- `u × id : ℂ × B ⟶ A × B`. -/
noncomputable def sq1h (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    OB (ULift.{u} ℂ × B) ⟶ OB (A × B) :=
  wProdMap (wUnit A) (idMap B)

/-- `id × u : A × ℂ ⟶ A × B`. -/
noncomputable def sq1i (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    OB (A × ULift.{u} ℂ) ⟶ OB (A × B) :=
  wProdMap (idMap A) (wUnit B)

@[simp] theorem sq1f_apply (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [Theses.VonNeumannAlgebra B]
    (y : ULift.{u} ℂ × ULift.{u} ℂ) :
    (sq1f B).toNCPMap y = (y.1, y.2.down • (1 : B)) := rfl

@[simp] theorem sq1g_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A]
    (y : ULift.{u} ℂ × ULift.{u} ℂ) :
    (sq1g A).toNCPMap y = (y.1.down • (1 : A), y.2) := rfl

@[simp] theorem sq1h_apply (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B]
    (y : ULift.{u} ℂ × B) :
    (sq1h A B).toNCPMap y = (y.1.down • (1 : A), y.2) := rfl

@[simp] theorem sq1i_apply (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B]
    (y : A × ULift.{u} ℂ) :
    (sq1i A B).toNCPMap y = (y.1, y.2.down • (1 : B)) := rfl

/-- **The left pullback square of 180I in `vNᵒᵖ`**: the square
```
  ℂ × ℂ --id×u--> ℂ × B
    |u×id           |u×id
    v               v
  A × ℂ --id×u--> A × B
```
is a pushout in `vN` — an ncpu-map out of `A × B` is precisely a pair of
ncpu-maps out of `ℂ × B` and `A × ℂ` agreeing on `ℂ × ℂ`, glued by
`γ(a, b) = β(a, 0) + α(0, b)`. -/
theorem vn_isPushout1 (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    IsPushout (sq1f B) (sq1g A) (sq1h A B) (sq1i A B) := by
  have w : sq1f B ≫ sq1h A B = sq1g A ≫ sq1i A B :=
    vn_hom_ext fun x => (vn_comp_apply _ _ x).trans (vn_comp_apply _ _ x).symm
  have hcond : ∀ s : PushoutCocone (sq1f B) (sq1g A), ∀ z w : ULift.{u} ℂ,
      s.inl.toNCPMap (z, w.down • (1 : B))
        = s.inr.toNCPMap (z.down • (1 : A), w) := by
    intro s z w
    exact ((vn_comp_apply (sq1f B) s.inl (z, w)).symm.trans
      (vn_congr s.condition (z, w))).trans (vn_comp_apply (sq1g A) s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => med1 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact vn_hom_ext fun y =>
      (vn_comp_apply (sq1h A B) _ y).trans (med1_fac_left _ _ (hcond s) y)
  · intro s
    exact vn_hom_ext fun y =>
      (vn_comp_apply (sq1i A B) _ y).trans (med1_fac_right _ _ (hcond s) y)
  · intro s m h₁ h₂
    refine med1_uniq _ _ (hcond s) m (fun y => ?_) (fun y => ?_)
    · exact (vn_comp_apply (sq1h A B) m y).symm.trans (vn_congr h₁ y)
    · exact (vn_comp_apply (sq1i A B) m y).symm.trans (vn_congr h₂ y)

end

section

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A positive map on a product algebra killing `(0, 1)` kills all of
`0 × B`: for `0 ≤ b` one has `(0, b) ≤ ‖b‖ · (0, 1)`, and every element is a
linear combination of positive ones. -/
theorem prod_apply_eq_zero (α : Theses.NCPUMap (A × B) C)
    (h1 : α.toNCPMap ((0 : A), (1 : B)) = 0) (b : B) :
    α.toNCPMap ((0 : A), b) = 0 := by
  have hnn : ∀ c : B, 0 ≤ c → α.toNCPMap ((0 : A), c) = 0 := by
    intro c hc
    have hle : ((0 : A), c) ≤ ((0 : A), (‖c‖ : ℝ) • (1 : B)) :=
      Prod.le_def.mpr ⟨le_refl _, Theses.A.VN.le_norm_smul_one hc⟩
    have h0 : (0 : A × B) ≤ ((0 : A), c) := Prod.le_def.mpr ⟨le_refl _, hc⟩
    have hmono := OrderHomClass.mono α.toNCPMap.toCompletelyPositiveMap hle
    have hpos := OrderHomClass.mono α.toNCPMap.toCompletelyPositiveMap h0
    have hsm : ((0 : A), (‖c‖ : ℝ) • (1 : B))
        = ((‖c‖ : ℝ) : ℂ) • (((0 : A), (1 : B)) : A × B) := by
      refine Prod.ext ?_ ?_ <;> simp [Complex.coe_smul]
    have hz : α.toNCPMap ((0 : A), (‖c‖ : ℝ) • (1 : B)) = 0 := by
      rw [hsm]
      have := map_smul (ncpLin α.toNCPMap) (((‖c‖ : ℝ) : ℂ))
        (((0 : A), (1 : B)) : A × B)
      rw [show α.toNCPMap ((((‖c‖ : ℝ) : ℂ)) • (((0 : A), (1 : B)) : A × B))
        = ncpLin α.toNCPMap ((((‖c‖ : ℝ) : ℂ)) • (((0 : A), (1 : B)) : A × B)) from rfl,
        this]
      rw [show ncpLin α.toNCPMap (((0 : A), (1 : B)) : A × B)
        = α.toNCPMap ((0 : A), (1 : B)) from rfl, h1, smul_zero]
    refine le_antisymm ?_ ?_
    · rw [← hz]; exact hmono
    · rw [map_zero] at hpos
      exact hpos
  exact linear_eq_zero_of_nonneg
    (f := (ncpLin α.toNCPMap).comp (LinearMap.inr ℂ A B)) hnn b

/-- The mediating ncpu-map `γ(a) = α(a, 0)` of the second pushout square. -/
noncomputable def med2 (α : Theses.NCPUMap (A × B) C)
    (β : Theses.NCPUMap (ULift.{u} ℂ) C)
    (hc : ∀ z w : ULift.{u} ℂ,
      α.toNCPMap (z.down • (1 : A), w.down • (1 : B)) = β.toNCPMap z) :
    Theses.NCPUMap A C :=
  mkNCPU ((ncpLin α.toNCPMap).comp (LinearMap.inl ℂ A B))
    (cp_comp _ _ cp_inlLin (ncpLin_cp _))
    (preservesDirSups_comp' (f := fun a : A => ((a, 0) : A × B))
      (g := ⇑(ncpLin α.toNCPMap)) preservesDirSups_inlFun
      (fun a => sa_prod a.2 (star_zero _)) (ncpLin_normal _))
    (by
      have hβ0 : β.toNCPMap 0 = 0 := by
        have := map_zero (ncpLin β.toNCPMap)
        exact this
      have h01 : α.toNCPMap ((0 : A), (1 : B)) = 0 := by
        have h := hc 0 1
        rw [hβ0] at h
        simpa using h
      have h2 := map_add (ncpLin α.toNCPMap) (((1 : A), (0 : B)) : A × B)
        (((0 : A), (1 : B)) : A × B)
      have h3 : (((1 : A), (0 : B)) : A × B) + (((0 : A), (1 : B)) : A × B)
          = (1 : A × B) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [h3] at h2
      show α.toNCPMap ((1 : A), (0 : B)) = 1
      have h4 : α.toNCPMap (1 : A × B)
          = α.toNCPMap ((1 : A), (0 : B)) + α.toNCPMap ((0 : A), (1 : B)) := h2
      rw [h01, add_zero, α.unital'] at h4
      exact h4.symm)

@[simp] theorem med2_apply (α : Theses.NCPUMap (A × B) C)
    (β : Theses.NCPUMap (ULift.{u} ℂ) C) (hc) (a : A) :
    (med2 α β hc).toNCPMap a = α.toNCPMap (a, 0) := rfl

section Med2

variable (α : Theses.NCPUMap (A × B) C) (β : Theses.NCPUMap (ULift.{u} ℂ) C)
  (hc : ∀ z w : ULift.{u} ℂ,
    α.toNCPMap (z.down • (1 : A), w.down • (1 : B)) = β.toNCPMap z)

theorem med2_fac_left (x : A × B) :
    (med2 α β hc).toNCPMap x.1 = α.toNCPMap x := by
  show α.toNCPMap (x.1, 0) = α.toNCPMap x
  have hβ0 : β.toNCPMap 0 = 0 := map_zero (ncpLin β.toNCPMap)
  have h01 : α.toNCPMap ((0 : A), (1 : B)) = 0 := by
    have h := hc 0 1
    rw [hβ0] at h
    simpa using h
  have h2 := map_add (ncpLin α.toNCPMap) ((x.1, (0 : B)) : A × B)
    (((0 : A), x.2) : A × B)
  have h3 : ((x.1, (0 : B)) : A × B) + (((0 : A), x.2) : A × B) = x := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h3] at h2
  have h4 : α.toNCPMap x
      = α.toNCPMap ((x.1, (0 : B)) : A × B) + α.toNCPMap (((0 : A), x.2) : A × B) := h2
  rw [prod_apply_eq_zero α h01 x.2, add_zero] at h4
  exact h4.symm

theorem med2_fac_right (z : ULift.{u} ℂ) :
    (med2 α β hc).toNCPMap (z.down • (1 : A)) = β.toNCPMap z := by
  show α.toNCPMap (z.down • (1 : A), 0) = β.toNCPMap z
  have h := hc z 0
  simpa using h

theorem med2_uniq (m : Theses.NCPUMap A C)
    (h₁ : ∀ x : A × B, m.toNCPMap x.1 = α.toNCPMap x) : m = med2 α β hc := by
  refine ncpu_ext fun a => ?_
  show m.toNCPMap a = α.toNCPMap (a, 0)
  exact h₁ ((a, (0 : B)) : A × B)

end Med2

end

section

/-! ### The right pullback square of 180I -/

/-- `u × u : ℂ × ℂ ⟶ A × B`. -/
noncomputable def sq2f (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    OB (ULift.{u} ℂ × ULift.{u} ℂ) ⟶ OB (A × B) :=
  wProdMap (wUnit A) (wUnit B)

/-- `π₁ : ℂ × ℂ ⟶ ℂ`. -/
noncomputable def sq2g : OB (ULift.{u} ℂ × ULift.{u} ℂ) ⟶ OB (ULift.{u} ℂ) :=
  wFst (ULift.{u} ℂ) (ULift.{u} ℂ)

/-- `π₁ : A × B ⟶ A`. -/
noncomputable def sq2h (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    OB (A × B) ⟶ OB A := wFst A B

/-- `u : ℂ ⟶ A`. -/
noncomputable def sq2i (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    OB (ULift.{u} ℂ) ⟶ OB A := wUnit A

/-- **The right pullback square of 180I in `vNᵒᵖ`**: the square
```
  ℂ × ℂ --u×u--> A × B
    |π₁            |π₁
    v              v
    ℂ  ---u----->  A
```
is a pushout in `vN`.  The mediating map is `γ(a) = α(a, 0)`; that it is
well defined uses that a positive map killing `(0,1)` kills `0 × B`. -/
theorem vn_isPushout2 (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B] :
    IsPushout (sq2f A B) sq2g (sq2h A B) (sq2i A) := by
  have w : sq2f A B ≫ sq2h A B = sq2g ≫ sq2i A :=
    vn_hom_ext fun x => (vn_comp_apply _ _ x).trans (vn_comp_apply _ _ x).symm
  have hcond : ∀ s : PushoutCocone (sq2f A B) sq2g, ∀ z w : ULift.{u} ℂ,
      s.inl.toNCPMap (z.down • (1 : A), w.down • (1 : B)) = s.inr.toNCPMap z := by
    intro s z w
    exact ((vn_comp_apply (sq2f A B) s.inl (z, w)).symm.trans
      (vn_congr s.condition (z, w))).trans (vn_comp_apply sq2g s.inr (z, w))
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => med2 s.inl s.inr (hcond s)) ?_ ?_ ?_)
  · intro s
    exact vn_hom_ext fun x =>
      (vn_comp_apply (sq2h A B) _ x).trans (med2_fac_left _ _ (hcond s) x)
  · intro s
    exact vn_hom_ext fun z =>
      (vn_comp_apply (sq2i A) _ z).trans (med2_fac_right _ _ (hcond s) z)
  · intro s m h₁ h₂
    exact med2_uniq _ _ (hcond s) m
      (fun x => (vn_comp_apply (sq2h A B) m x).symm.trans (vn_congr h₁ x))

/-! ### Joint monicity of the two cotuples -/

/-- **The third axiom of 180I in `vNᵒᵖ`**, elementwise: an ncpu-map out of
`ℂ³` is determined by its restrictions along `(x,y) ↦ (x,y,y)` and
`(x,y) ↦ (y,x,y)`, because those recover the images of the three minimal
projections. -/
theorem vn_jointlyMonic_aux {Z : Type u} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z]
    (a b : Theses.NCPUMap ((ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ) Z)
    (h1 : ∀ x : ULift.{u} ℂ × ULift.{u} ℂ,
      a.toNCPMap ((x.1, x.2), x.2) = b.toNCPMap ((x.1, x.2), x.2))
    (h2 : ∀ x : ULift.{u} ℂ × ULift.{u} ℂ,
      a.toNCPMap ((x.2, x.1), x.2) = b.toNCPMap ((x.2, x.1), x.2)) :
    a = b := by
  set e₁ : (ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ := ((1, 0), 0) with he₁
  set e₂ : (ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ := ((0, 1), 0) with he₂
  set e₃ : (ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ := ((0, 0), 1) with he₃
  have ha1 : a.toNCPMap e₁ = b.toNCPMap e₁ := h1 (1, 0)
  have ha2 : a.toNCPMap e₂ = b.toNCPMap e₂ := h2 (1, 0)
  have ha3 : a.toNCPMap e₃ = b.toNCPMap e₃ := by
    have h4 := h1 (0, 1)
    have hsum : (((0 : ULift.{u} ℂ), (1 : ULift.{u} ℂ)), (1 : ULift.{u} ℂ))
        = e₂ + e₃ := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [he₂, he₃]
    rw [hsum] at h4
    have hA := map_add (ncpLin a.toNCPMap) e₂ e₃
    have hB := map_add (ncpLin b.toNCPMap) e₂ e₃
    have h5 : a.toNCPMap e₂ + a.toNCPMap e₃ = b.toNCPMap e₂ + b.toNCPMap e₃ := by
      rw [show a.toNCPMap e₂ + a.toNCPMap e₃
        = ncpLin a.toNCPMap e₂ + ncpLin a.toNCPMap e₃ from rfl, ← hA,
        show b.toNCPMap e₂ + b.toNCPMap e₃
        = ncpLin b.toNCPMap e₂ + ncpLin b.toNCPMap e₃ from rfl, ← hB]
      exact h4
    rw [ha2] at h5
    exact add_left_cancel h5
  have key : ∀ (f : Theses.NCPUMap ((ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ) Z)
      (y : (ULift.{u} ℂ × ULift.{u} ℂ) × ULift.{u} ℂ),
      f.toNCPMap y = y.1.1.down • f.toNCPMap e₁
        + (y.1.2.down • f.toNCPMap e₂ + y.2.down • f.toNCPMap e₃) := by
    intro f y
    have hdec : y = y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · apply Theses.A.VN.CU.down_injective
          simp [he₁, he₂, he₃]
    conv_lhs => rw [hdec]
    rw [show f.toNCPMap (y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃))
      = ncpLin f.toNCPMap (y.1.1.down • e₁ + (y.1.2.down • e₂ + y.2.down • e₃))
      from rfl, map_add, map_smul, map_add, map_smul, map_smul]
    rfl
  refine ncpu_ext fun y => ?_
  rw [key a y, key b y, ha1, ha2, ha3]

end

section

theorem vnPres_from_apply (Y : WStarNCPU.{u}ᵒᵖ) (z : ULift.{u} ℂ) :
    (vnPres.hT.from Y).unop.toNCPMap z = z.down • (1 : Y.unop.base.carrier) := by
  have h : vnPres.hT.from Y = Quiver.Hom.op (wUnit Y.unop.base.carrier) :=
    vnPres.hT.hom_ext _ _
  rw [h]
  rfl

theorem vnPres_pmap_apply {X X' Y Y' : WStarNCPU.{u}ᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : (vnPres.P X' Y').unop.base.carrier) :
    (vnPres.pmap f g).unop.toNCPMap x
      = (f.unop.toNCPMap x.1, g.unop.toNCPMap x.2) := by
  refine Prod.ext ?_ ?_
  · exact vnop_comp_apply f _ x
  · exact vnop_comp_apply g _ x

end

end VNEffectus

/-! ## `vNᵒᵖ` is an effectus (parsec 180)

The A-dependent statements of `Effectus.lean`. -/

/-- **180V** (`effectus-vn`, eff.tex:827) and **189aI**
(`effexamplesintro`, eff.tex:2020, Examples): the main example — the
opposite `vNᵒᵖ` of the category of von Neumann algebras with ncpu-maps is
an effectus in total form. -/
theorem effectus_vn : Nonempty (EffectusTotalStructure WStarNCPU.{u}ᵒᵖ) := by
  have : HasTerminal (WStarNCPU.{u}ᵒᵖ) := vnPres.hT.hasTerminal
  have : HasInitial (WStarNCPU.{u}ᵒᵖ) :=
    (IsTerminal.op (WStarNCPU.{u}) vnTrivIsTerminal).hasInitial
  have : ∀ X Y : WStarNCPU.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, vnPres.hP X Y⟩
  have : HasBinaryCoproducts (WStarNCPU.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  have : HasFiniteCoproducts (WStarNCPU.{u}ᵒᵖ) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  refine ⟨{ hasFiniteCoproducts := inferInstance
            hasTerminal := inferInstance
            effectus := effectusTotalForm_of_pres vnPres ?_ ?_ ?_ }⟩
  · intro X Y
    have e₁ : vnPres.pmap (𝟙 X) (vnPres.hT.from Y)
        = Quiver.Hom.op (sq1i X.unop.base.carrier Y.unop.base.carrier) := by
      refine vnop_hom_ext fun x => (vnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact vn_id_apply x.1
      · exact vnPres_from_apply Y x.2
    have e₂ : vnPres.pmap (vnPres.hT.from X) (𝟙 Y)
        = Quiver.Hom.op (sq1h X.unop.base.carrier Y.unop.base.carrier) := by
      refine vnop_hom_ext fun x => (vnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact vnPres_from_apply X x.1
      · exact vn_id_apply x.2
    have e₃ : vnPres.pmap (vnPres.hT.from X) (𝟙 vnPres.T)
        = Quiver.Hom.op (sq1g X.unop.base.carrier) := by
      refine vnop_hom_ext fun x => (vnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact vnPres_from_apply X x.1
      · exact vn_id_apply x.2
    have e₄ : vnPres.pmap (𝟙 vnPres.T) (vnPres.hT.from Y)
        = Quiver.Hom.op (sq1f Y.unop.base.carrier) := by
      refine vnop_hom_ext fun x => (vnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact vn_id_apply x.1
      · exact vnPres_from_apply Y x.2
    rw [e₁, e₂, e₃, e₄]
    exact (vn_isPushout1 X.unop.base.carrier Y.unop.base.carrier).op
  · intro X Y
    have f₁ : vnPres.hT.from X = Quiver.Hom.op (sq2i X.unop.base.carrier) :=
      vnPres.hT.hom_ext _ _
    have f₄ : vnPres.pmap (vnPres.hT.from X) (vnPres.hT.from Y)
        = Quiver.Hom.op (sq2f X.unop.base.carrier Y.unop.base.carrier) := by
      refine vnop_hom_ext fun x => (vnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact vnPres_from_apply X x.1
      · exact vnPres_from_apply Y x.2
    rw [f₄, f₁]
    exact (vn_isPushout2 X.unop.base.carrier Y.unop.base.carrier).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    refine vn_jointlyMonic_aux a.unop b.unop (fun x => ?_) (fun x => ?_)
    · exact vnop_comp_congr hf x
    · exact vnop_comp_congr hg x

/-! ### `CvNᵒᵖ`, the commutative full subcategory (189aI, second sentence)

The second sentence of 189aI — "its full subcategory `CvNᵒᵖ` of commutative
von Neumann algebras is an effectus as well".  Nothing has to be re-proved
about von Neumann algebras: `ℂᵤ` and a product of commutative algebras are
commutative, so the concrete presentation `vnPres` of `vNᵒᵖ` restricts to
`CvNᵒᵖ`, and the three axioms of 180I are pulled back from `vNᵒᵖ` along the
inclusion, which is fully faithful and therefore reflects pullbacks. -/

/-- Commutativity of the carrier, as a property of the objects of `vN`. -/
def IsCommWStar : ObjectProperty WStarNCPU.{u} :=
  fun A => ∀ x y : A.base.carrier, x * y = y * x

/-- **`CvN`**: the full subcategory of `vN` spanned by the commutative von
Neumann algebras (the morphisms are still all ncpu-maps). -/
abbrev CWStarNCPU : Type (u + 1) := IsCommWStar.{u}.FullSubcategory

/-- The scalars `ℂᵤ` as an object of `CvN`. -/
noncomputable def cvnScal : CWStarNCPU.{u} :=
  ⟨OB (ULift.{u} ℂ), fun x y => Theses.A.VN.CU.down_injective (mul_comm x.down y.down)⟩

/-- The product of two commutative von Neumann algebras, as an object of
`CvN` (the effectus coproduct of `CvNᵒᵖ`). -/
noncomputable def cvnProd (X Y : CWStarNCPU.{u}) : CWStarNCPU.{u} :=
  ⟨OB (X.obj.base.carrier × Y.obj.base.carrier),
    fun x y => Prod.ext (X.property x.1 y.1) (Y.property x.2 y.2)⟩

/-- The trivial algebra as an object of `CvN`. -/
noncomputable def cvnTriv : CWStarNCPU.{u} :=
  ⟨OB PUnit.{u + 1}, fun _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _⟩

theorem cvn_hom_ext {X Y : CWStarNCPU.{u}} {f g : X ⟶ Y}
    (h : ∀ a, f.hom.toNCPMap a = g.hom.toNCPMap a) : f = g :=
  InducedCategory.hom_ext (vn_hom_ext h)

theorem cvnop_hom_ext {X Y : CWStarNCPU.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ a, f.unop.hom.toNCPMap a = g.unop.hom.toNCPMap a) : f = g :=
  Quiver.Hom.unop_inj (cvn_hom_ext h)

theorem cvnop_comp_apply {X Y Z : CWStarNCPU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Z.unop.obj.base) :
    (f ≫ g).unop.hom.toNCPMap a = f.unop.hom.toNCPMap (g.unop.hom.toNCPMap a) :=
  vn_comp_apply g.unop.hom f.unop.hom a

theorem cvnop_congr {X Y : CWStarNCPU.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (a : Y.unop.obj.base) : f.unop.hom.toNCPMap a = g.unop.hom.toNCPMap a := by
  rw [h]

theorem cvn_id_apply {X : CWStarNCPU.{u}} (a : X.obj.base) :
    (𝟙 X : X ⟶ X).hom.toNCPMap a = a := vn_id_apply a

/-- Postcomposition with a fixed map, pointwise. -/
theorem cvnop_comp_congr {Z P X : CWStarNCPU.{u}ᵒᵖ} {F : P ⟶ X} {a b : Z ⟶ P}
    (h : a ≫ F = b ≫ F) (x : X.unop.obj.base) :
    a.unop.hom.toNCPMap (F.unop.hom.toNCPMap x)
      = b.unop.hom.toNCPMap (F.unop.hom.toNCPMap x) :=
  ((cvnop_comp_apply a F x).symm.trans (cvnop_congr h x)).trans
    (cvnop_comp_apply b F x)

/-- `ℂᵤ` is initial in `CvN`, hence final in `CvNᵒᵖ`. -/
noncomputable def cvnScalIsInitial : IsInitial (cvnScal.{u}) :=
  IsInitial.ofUniqueHom
    (fun X => InducedCategory.homMk (wUnit X.obj.base.carrier))
    (fun _ f => InducedCategory.hom_ext (wUnit_unique f.hom))

/-- The trivial algebra is final in `CvN`, hence initial in `CvNᵒᵖ`. -/
noncomputable def cvnTrivIsTerminal : IsTerminal (cvnTriv.{u}) :=
  IsTerminal.ofUniqueHom (fun X => InducedCategory.homMk (wTriv X.obj.base.carrier))
    (fun _ _ => InducedCategory.hom_ext
      (ncpu_ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _))

/-- The concrete presentation of `CvNᵒᵖ`, the restriction of `vnPres`: the
final object is `ℂᵤ`, the binary coproducts are the products. -/
noncomputable def cvnPres : CoprodPres (CWStarNCPU.{u}ᵒᵖ) where
  T := Opposite.op cvnScal
  hT := IsInitial.op (CWStarNCPU.{u}) cvnScalIsInitial
  P X Y := Opposite.op (cvnProd X.unop Y.unop)
  pinl X Y := Quiver.Hom.op
    (InducedCategory.homMk (wFst X.unop.obj.base.carrier Y.unop.obj.base.carrier))
  pinr X Y := Quiver.Hom.op
    (InducedCategory.homMk (wSnd X.unop.obj.base.carrier Y.unop.obj.base.carrier))
  hP X Y := BinaryCofan.IsColimit.mk _
    (fun {_} u v => Quiver.Hom.op
      (InducedCategory.homMk (wPair u.unop.hom v.unop.hom)))
    (fun {_} _ _ => cvnop_hom_ext fun a => cvnop_comp_apply _ _ a)
    (fun {_} _ _ => cvnop_hom_ext fun a => cvnop_comp_apply _ _ a)
    (fun {_} _ _ m h₁ h₂ => cvnop_hom_ext fun a => by
      refine Prod.ext ?_ ?_
      · exact (cvnop_comp_apply _ m a).symm.trans (cvnop_congr h₁ a)
      · exact (cvnop_comp_apply _ m a).symm.trans (cvnop_congr h₂ a))

theorem cvnPres_from_apply (Y : CWStarNCPU.{u}ᵒᵖ) (z : ULift.{u} ℂ) :
    (cvnPres.hT.from Y).unop.hom.toNCPMap z
      = z.down • (1 : Y.unop.obj.base.carrier) := by
  have h : cvnPres.hT.from Y
      = Quiver.Hom.op (InducedCategory.homMk (wUnit Y.unop.obj.base.carrier)) :=
    cvnPres.hT.hom_ext _ _
  rw [h]
  rfl

theorem cvnPres_pmap_apply {X X' Y Y' : CWStarNCPU.{u}ᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : (cvnPres.P X' Y').unop.obj.base.carrier) :
    (cvnPres.pmap f g).unop.hom.toNCPMap x
      = (f.unop.hom.toNCPMap x.1, g.unop.hom.toNCPMap x.2) := by
  refine Prod.ext ?_ ?_
  · exact cvnop_comp_apply f _ x
  · exact cvnop_comp_apply g _ x

/-- **189aI** (`effexamplesintro`, eff.tex:2020, Examples), second sentence:
the full subcategory `CvNᵒᵖ` of `vNᵒᵖ` on the commutative von Neumann
algebras is an effectus in total form as well.

The point gives no proof.  Ours restricts the presentation `vnPres` to
`CvNᵒᵖ` — `ℂᵤ` is commutative and so is a product of commutative algebras,
so the final object and the binary coproducts of `vNᵒᵖ` stay inside the
subcategory — and then pulls the three axioms of 180I back along the
inclusion `CvNᵒᵖ ⥤ vNᵒᵖ`, which is fully faithful and therefore reflects
pullbacks (`IsPullback.of_map_of_faithful`).  So `vn_isPushout1`,
`vn_isPushout2` and `vn_jointlyMonic_aux` are reused verbatim; no von
Neumann algebra theory is redone. -/
theorem effectus_cvn : Nonempty (EffectusTotalStructure CWStarNCPU.{u}ᵒᵖ) := by
  have : HasTerminal (CWStarNCPU.{u}ᵒᵖ) := cvnPres.hT.hasTerminal
  have : HasInitial (CWStarNCPU.{u}ᵒᵖ) :=
    (IsTerminal.op (CWStarNCPU.{u}) cvnTrivIsTerminal).hasInitial
  have : ∀ X Y : CWStarNCPU.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, cvnPres.hP X Y⟩
  have : HasBinaryCoproducts (CWStarNCPU.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  have : HasFiniteCoproducts (CWStarNCPU.{u}ᵒᵖ) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  refine ⟨{ hasFiniteCoproducts := inferInstance
            hasTerminal := inferInstance
            effectus := effectusTotalForm_of_pres cvnPres ?_ ?_ ?_ }⟩
  · intro X Y
    refine IsPullback.of_map_of_faithful (IsCommWStar.{u}.ι.op) ?_
    have e₁ : (IsCommWStar.{u}.ι.op).map (cvnPres.pmap (𝟙 X) (cvnPres.hT.from Y))
        = Quiver.Hom.op (sq1i X.unop.obj.base.carrier Y.unop.obj.base.carrier) := by
      refine vnop_hom_ext fun x => (cvnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact cvn_id_apply x.1
      · exact cvnPres_from_apply Y x.2
    have e₂ : (IsCommWStar.{u}.ι.op).map (cvnPres.pmap (cvnPres.hT.from X) (𝟙 Y))
        = Quiver.Hom.op (sq1h X.unop.obj.base.carrier Y.unop.obj.base.carrier) := by
      refine vnop_hom_ext fun x => (cvnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact cvnPres_from_apply X x.1
      · exact cvn_id_apply x.2
    have e₃ : (IsCommWStar.{u}.ι.op).map
          (cvnPres.pmap (cvnPres.hT.from X) (𝟙 cvnPres.T))
        = Quiver.Hom.op (sq1g X.unop.obj.base.carrier) := by
      refine vnop_hom_ext fun x => (cvnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact cvnPres_from_apply X x.1
      · exact cvn_id_apply x.2
    have e₄ : (IsCommWStar.{u}.ι.op).map
          (cvnPres.pmap (𝟙 cvnPres.T) (cvnPres.hT.from Y))
        = Quiver.Hom.op (sq1f Y.unop.obj.base.carrier) := by
      refine vnop_hom_ext fun x => (cvnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact cvn_id_apply x.1
      · exact cvnPres_from_apply Y x.2
    rw [e₁, e₂, e₃, e₄]
    exact (vn_isPushout1 X.unop.obj.base.carrier Y.unop.obj.base.carrier).op
  · intro X Y
    refine IsPullback.of_map_of_faithful (IsCommWStar.{u}.ι.op) ?_
    have f₁ : (IsCommWStar.{u}.ι.op).map (cvnPres.hT.from X)
        = Quiver.Hom.op (sq2i X.unop.obj.base.carrier) :=
      vnop_hom_ext fun z => cvnPres_from_apply X z
    have f₄ : (IsCommWStar.{u}.ι.op).map
          (cvnPres.pmap (cvnPres.hT.from X) (cvnPres.hT.from Y))
        = Quiver.Hom.op (sq2f X.unop.obj.base.carrier Y.unop.obj.base.carrier) := by
      refine vnop_hom_ext fun x => (cvnPres_pmap_apply _ _ x).trans ?_
      refine Prod.ext ?_ ?_
      · exact cvnPres_from_apply X x.1
      · exact cvnPres_from_apply Y x.2
    rw [f₄, f₁]
    exact (vn_isPushout2 X.unop.obj.base.carrier Y.unop.obj.base.carrier).op
  · intro Z a b hf hg
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    refine vn_jointlyMonic_aux a.unop.hom b.unop.hom (fun x => ?_) (fun x => ?_)
    · exact cvnop_comp_congr hf x
    · exact cvnop_comp_congr hg x

/-! ## Infrastructure for the partial form (180V)

The ncpsu-map counterpart of the block above: the category `vN_cpsu`, its
finite products, the PCM enrichment `f ⊥ g ⟺ f(1) + g(1) ≤ 1`,
`f ⋁ g = f + g`, and the effects `Pred 𝒜 = [0,1]_𝒜`. -/

section VNPartial

open Theses.A.CStar
open scoped ComplexOrder ComplexStarModule

section SUMaps

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- Extensionality for ncpsu-maps. -/
theorem ncpsu_ext {f g : Theses.NCPSUMap A B}
    (h : ∀ a, f.toNCPMap a = g.toNCPMap a) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hfg : f = g := DFunLike.coe_injective (funext h)
  subst hfg
  rfl

/-- An ncpsu-map from a linear map that is completely positive, normal and
subunital. -/
noncomputable def mkNCPSU (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) (hsu : f 1 ≤ 1) : Theses.NCPSUMap A B :=
  ⟨mkNCP f hcp hn, hsu⟩

@[simp] theorem mkNCPSU_apply (f : A →ₗ[ℂ] B) (hcp : IsCompletelyPositiveMap f)
    (hn : Theses.PreservesDirSups ⇑f) (hsu : f 1 ≤ 1) (a : A) :
    (mkNCPSU f hcp hn hsu).toNCPMap a = f a := rfl

theorem ncp_add_apply (f : Theses.NCPMap A B) (x y : A) :
    f (x + y) = f x + f y := map_add (ncpLin f) x y

theorem ncp_zero_apply (f : Theses.NCPMap A B) : f 0 = 0 := map_zero (ncpLin f)

theorem ncp_smul_apply (f : Theses.NCPMap A B) (r : ℂ) (x : A) :
    f (r • x) = r • f x := map_smul (ncpLin f) r x

/-- The zero map is completely positive. -/
theorem cp_zeroLin : IsCompletelyPositiveMap (0 : A →ₗ[ℂ] B) := by
  intro n a b
  simp

/-- The zero map is normal. -/
theorem preservesDirSups_zeroFun :
    Theses.PreservesDirSups (fun _ : A => (0 : B)) := by
  intro D s hne _ _
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact le_refl 0
  · intro c hc
    obtain ⟨d, hd⟩ := hne
    exact hc ⟨d, hd, rfl⟩

/-- The zero ncpsu-map. -/
noncomputable def wZeroSU (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Theses.NCPSUMap A B :=
  mkNCPSU 0 cp_zeroLin preservesDirSups_zeroFun (by simpa using zero_le_one' B)

@[simp] theorem wZeroSU_apply (a : A) : (wZeroSU A B).toNCPMap a = 0 := rfl

/-- The sum of two ncpsu-maps, when it is again subunital. -/
noncomputable def wAddSU (f g : Theses.NCPSUMap A B)
    (h : f.toNCPMap 1 + g.toNCPMap 1 ≤ 1) : Theses.NCPSUMap A B :=
  mkNCPSU (ncpLin f.toNCPMap + ncpLin g.toNCPMap)
    (cp_add (ncpLin_cp _) (ncpLin_cp _))
    (preservesDirSups_add (ncpLin_normal _) (ncpLin_normal _)) h

@[simp] theorem wAddSU_apply (f g : Theses.NCPSUMap A B)
    (h : f.toNCPMap 1 + g.toNCPMap 1 ≤ 1) (a : A) :
    (wAddSU f g h).toNCPMap a = f.toNCPMap a + g.toNCPMap a := rfl

/-- The first projection as an ncpsu-map. -/
noncomputable def wFstSU (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Theses.NCPSUMap (A × B) A :=
  mkNCPSU (LinearMap.fst ℂ A B) cp_fstLin preservesDirSups_fstFun (le_refl 1)

/-- The second projection as an ncpsu-map. -/
noncomputable def wSndSU (A B : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Theses.NCPSUMap (A × B) B :=
  mkNCPSU (LinearMap.snd ℂ A B) cp_sndLin preservesDirSups_sndFun (le_refl 1)

@[simp] theorem wFstSU_apply (x : A × B) : (wFstSU A B).toNCPMap x = x.1 := rfl
@[simp] theorem wSndSU_apply (x : A × B) : (wSndSU A B).toNCPMap x = x.2 := rfl

/-- The pairing of two ncpsu-maps. -/
noncomputable def wPairSU (f : Theses.NCPSUMap C A) (g : Theses.NCPSUMap C B) :
    Theses.NCPSUMap C (A × B) :=
  mkNCPSU (LinearMap.prod (ncpLin f.toNCPMap) (ncpLin g.toNCPMap))
    (cp_prod (ncpLin_cp _) (ncpLin_cp _))
    (preservesDirSups_prodFun (ncpLin_normal _) (ncpLin_normal _))
    (Prod.le_def.mpr ⟨f.subunital', g.subunital'⟩)

@[simp] theorem wPairSU_apply (f : Theses.NCPSUMap C A) (g : Theses.NCPSUMap C B)
    (c : C) : (wPairSU f g).toNCPMap c = (f.toNCPMap c, g.toNCPMap c) := rfl

/-- The ncpsu-map `ℂᵤ → A`, `z ↦ z·a`, for an effect `a`. -/
noncomputable def wEffect {a : A} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Theses.NCPSUMap (ULift.{u} ℂ) A :=
  ⟨Theses.A.VN.ncpOfNonneg h0, by
    show (1 : ULift.{u} ℂ).down • a ≤ 1
    simpa using h1⟩

@[simp] theorem wEffect_apply {a : A} (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (z : ULift.{u} ℂ) : (wEffect h0 h1).toNCPMap z = z.down • a := rfl

/-- An ncpsu-map out of the scalars is determined by its value at `1`. -/
theorem ncpsu_scal_ext {f g : Theses.NCPSUMap (ULift.{u} ℂ) A}
    (h : f.toNCPMap 1 = g.toNCPMap 1) : f = g := by
  refine ncpsu_ext fun z => ?_
  have hz : (z.down • (1 : ULift.{u} ℂ)) = z :=
    Theses.A.VN.CU.down_injective (by simp)
  have hf : f.toNCPMap (z.down • (1 : ULift.{u} ℂ)) = z.down • f.toNCPMap 1 :=
    map_smul (ncpLin f.toNCPMap) z.down 1
  have hg : g.toNCPMap (z.down • (1 : ULift.{u} ℂ)) = z.down • g.toNCPMap 1 :=
    map_smul (ncpLin g.toNCPMap) z.down 1
  conv_lhs => rw [← hz]
  conv_rhs => rw [← hz]
  rw [hf, hg, h]

/-- A normal completely positive map killing `1` is zero. -/
theorem ncp_eq_zero_of_one (f : Theses.NCPMap A B) (h1 : f 1 = 0) (a : A) :
    f a = 0 := by
  have hnn : ∀ c : A, 0 ≤ c → f c = 0 := by
    intro c hc
    have hle : c ≤ (‖c‖ : ℝ) • (1 : A) := Theses.A.VN.le_norm_smul_one hc
    have hmono := OrderHomClass.mono f.toCompletelyPositiveMap hle
    have hpos := OrderHomClass.mono f.toCompletelyPositiveMap hc
    rw [map_zero] at hpos
    have hz : f ((‖c‖ : ℝ) • (1 : A)) = 0 := by
      rw [show ((‖c‖ : ℝ) • (1 : A)) = ((‖c‖ : ℝ) : ℂ) • (1 : A) from by
        simp [Complex.coe_smul]]
      rw [show f (((‖c‖ : ℝ) : ℂ) • (1 : A))
        = ncpLin f (((‖c‖ : ℝ) : ℂ) • (1 : A)) from rfl,
        map_smul, show ncpLin f 1 = f 1 from rfl, h1, smul_zero]
    refine le_antisymm ?_ hpos
    rw [← hz]
    exact hmono
  exact linear_eq_zero_of_nonneg (f := ncpLin f) hnn a

end SUMaps

section SUCat

/-! ### The category `vN_cpsu` and its finite coproducts (in the opposite) -/

theorem su_hom_ext {X Y : WStarCPSU.{u}} {f g : X ⟶ Y}
    (h : ∀ a, f.toNCPMap a = g.toNCPMap a) : f = g := ncpsu_ext h

theorem su_comp_apply {X Y Z : WStarCPSU.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : X.base) : (f ≫ g).toNCPMap a = g.toNCPMap (f.toNCPMap a) :=
  (NCPSUMap.exists_comp f g).choose_spec a

theorem su_id_apply {X : WStarCPSU.{u}} (a : X.base) :
    (𝟙 X : Theses.NCPSUMap X.base.carrier X.base.carrier).toNCPMap a = a :=
  (NCPSUMap.exists_id X.base.carrier).choose_spec a

theorem suop_hom_ext {X Y : WStarCPSU.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : ∀ a, f.unop.toNCPMap a = g.unop.toNCPMap a) : f = g :=
  Quiver.Hom.unop_inj (su_hom_ext h)

theorem suop_comp_apply {X Y Z : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Z.unop.base) :
    (f ≫ g).unop.toNCPMap a = f.unop.toNCPMap (g.unop.toNCPMap a) :=
  su_comp_apply g.unop f.unop a

theorem suop_congr {X Y : WStarCPSU.{u}ᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (a : Y.unop.base) : f.unop.toNCPMap a = g.unop.toNCPMap a := by rw [h]

/-- The unique ncpsu-map into the trivial algebra. -/
noncomputable def wTrivSU (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPSUMap A PUnit.{u + 1} :=
  mkNCPSU 0 cp_zeroLin preservesDirSups_zeroFun (le_of_eq (Subsingleton.elim _ _))

/-- **The trivial algebra is the final object of `vN_cpsu`**, hence the
initial object of `vN_cpsuᵒᵖ`. -/
noncomputable def suTrivIsTerminal :
    IsTerminal (WStarCPSU.of (WStar.of PUnit.{u + 1})) :=
  IsTerminal.ofUniqueHom (fun X => wTrivSU X.base.carrier)
    (fun _ _ => ncpsu_ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _)

/-- The concrete binary coproduct `X + Y` of `vN_cpsuᵒᵖ`: the product
algebra. -/
noncomputable abbrev suP (X Y : WStarCPSU.{u}ᵒᵖ) : WStarCPSU.{u}ᵒᵖ :=
  Opposite.op (WStarCPSU.of (WStar.of
    (X.unop.base.carrier × Y.unop.base.carrier)))

/-- The first coprojection `κ₁ : X ⟶ X + Y` (the first projection of
`vN_cpsu`). -/
noncomputable def suPinl (X Y : WStarCPSU.{u}ᵒᵖ) : X ⟶ suP X Y :=
  Quiver.Hom.op (wFstSU X.unop.base.carrier Y.unop.base.carrier)

/-- The second coprojection `κ₂ : Y ⟶ X + Y`. -/
noncomputable def suPinr (X Y : WStarCPSU.{u}ᵒᵖ) : Y ⟶ suP X Y :=
  Quiver.Hom.op (wSndSU X.unop.base.carrier Y.unop.base.carrier)

/-- The cotupling `[f, g] : X + Y ⟶ Z` (the pairing of `vN_cpsu`). -/
noncomputable def suPdesc {X Y Z : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    suP X Y ⟶ Z :=
  Quiver.Hom.op (wPairSU f.unop g.unop)

/-- The product algebra is the binary coproduct of `vN_cpsuᵒᵖ`. -/
noncomputable def suHP (X Y : WStarCPSU.{u}ᵒᵖ) :
    IsColimit (BinaryCofan.mk (suPinl X Y) (suPinr X Y)) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => suPdesc u v)
    (fun {_} u v => suop_hom_ext fun a => suop_comp_apply _ _ a)
    (fun {_} u v => suop_hom_ext fun a => suop_comp_apply _ _ a)
    (fun {_} u v m h₁ h₂ => suop_hom_ext fun a => by
      refine Prod.ext ?_ ?_
      · exact (suop_comp_apply _ m a).symm.trans (suop_congr h₁ a)
      · exact (suop_comp_apply _ m a).symm.trans (suop_congr h₂ a))

/-- Finite coproducts of `vN_cpsuᵒᵖ`. -/
noncomputable def suHasFiniteCoproducts : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) :=
  letI : HasInitial (WStarCPSU.{u}ᵒᵖ) :=
    (IsTerminal.op (WStarCPSU.{u}) suTrivIsTerminal).hasInitial
  letI : ∀ X Y : WStarCPSU.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, suHP X Y⟩
  letI : HasBinaryCoproducts (WStarCPSU.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  hasFiniteCoproducts_of_has_binary_and_initial

/-! ### The PCM enrichment -/

theorem ncpsu_one_nonneg {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : Theses.NCPSUMap A B) : 0 ≤ f.toNCPMap 1 := by
  have h := OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap
    (zero_le_one' A)
  rwa [map_zero] at h

/-- **The PCM enrichment of `vN_cpsuᵒᵖ`**: `f ⊥ g` iff `f(1) + g(1) ≤ 1`
(i.e. iff the sum is again subunital), and then `f ⋁ g = f + g`. -/
noncomputable def suPCM (X Y : WStarCPSU.{u}ᵒᵖ) : PCM (X ⟶ Y) where
  zero := Quiver.Hom.op (wZeroSU Y.unop.base.carrier X.unop.base.carrier)
  Perp f g := f.unop.toNCPMap 1 + g.unop.toNCPMap 1 ≤ 1
  ovee f g h := Quiver.Hom.op (wAddSU f.unop g.unop h)
  perp_comm h := by rw [add_comm]; exact h
  ovee_comm h := suop_hom_ext fun a => add_comm _ _
  perp_of_ovee_perp := fun {a b c} hab h => by
    have h0 : 0 ≤ a.unop.toNCPMap 1 := ncpsu_one_nonneg _
    have h1 : b.unop.toNCPMap 1 ≤ a.unop.toNCPMap 1 + b.unop.toNCPMap 1 :=
      le_add_of_nonneg_left h0
    have h3 : b.unop.toNCPMap 1 + c.unop.toNCPMap 1
        ≤ (a.unop.toNCPMap 1 + b.unop.toNCPMap 1) + c.unop.toNCPMap 1 := by
      gcongr
    have h' : a.unop.toNCPMap 1 + b.unop.toNCPMap 1 + c.unop.toNCPMap 1 ≤ 1 := h
    exact le_trans h3 h'
  perp_ovee_of_ovee_perp := fun {a b c} hab h => by
    show a.unop.toNCPMap 1 + (b.unop.toNCPMap 1 + c.unop.toNCPMap 1) ≤ 1
    rw [← add_assoc]
    exact h
  ovee_assoc := fun {a b c} hab h => suop_hom_ext fun x => (add_assoc _ _ _)
  zero_perp a := by
    show (0 : X.unop.base.carrier) + a.unop.toNCPMap 1 ≤ 1
    rw [zero_add]
    exact a.unop.subunital'
  zero_ovee a := suop_hom_ext fun x => zero_add _

/-! ### The finPAC axioms and the effects -/

attribute [local instance] suHasFiniteCoproducts suPCM

theorem ncpsu_mono {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : Theses.NCPSUMap A B) {x y : A} (h : x ≤ y) :
    f.toNCPMap x ≤ f.toNCPMap y :=
  OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap h

theorem suPinl_desc {X Y Z : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    suPinl X Y ≫ suPdesc f g = f :=
  suop_hom_ext fun a => suop_comp_apply _ _ a

theorem suPinr_desc {X Y Z : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    suPinr X Y ≫ suPdesc f g = g :=
  suop_hom_ext fun a => suop_comp_apply _ _ a

/-- The comparison isomorphism between the ambient coproduct `X ⨿ Y` and the
concrete one. -/
noncomputable def suCoprodIso (X Y : WStarCPSU.{u}ᵒᵖ) : (X ⨿ Y) ≅ suP X Y :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso (suHP X Y)

theorem suInl_coprodIso (X Y : WStarCPSU.{u}ᵒᵖ) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ (suCoprodIso X Y).hom = suPinl X Y :=
  (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom (suHP X Y)
    ⟨WalkingPair.left⟩

theorem suInr_coprodIso (X Y : WStarCPSU.{u}ᵒᵖ) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ (suCoprodIso X Y).hom = suPinr X Y :=
  (coprodIsCoprod X Y).comp_coconePointUniqueUpToIso_hom (suHP X Y)
    ⟨WalkingPair.right⟩

/-- **`vN_cpsuᵒᵖ` is a finPAC** (180VII.1): composition is bilinear for the
pointwise sum, the compatible-sum axiom holds because `▷₁(1) + ▷₂(1) = 1` in
`𝒜 ⊕ 𝒜`, and untying because the coprojections are subunital. -/
theorem suFinPAC : FinPAC (WStarCPSU.{u}ᵒᵖ) where
  comp_ovee := fun {X Y Z f g} h k => by
    have hperp : (f ≫ k).unop.toNCPMap 1 + (g ≫ k).unop.toNCPMap 1 ≤ 1 := by
      rw [suop_comp_apply, suop_comp_apply]
      refine le_trans (add_le_add (ncpsu_mono f.unop k.unop.subunital')
        (ncpsu_mono g.unop k.unop.subunital')) h
    refine ⟨hperp, ?_⟩
    refine suop_hom_ext fun z => ?_
    rw [suop_comp_apply]
    show f.unop.toNCPMap (k.unop.toNCPMap z) + g.unop.toNCPMap (k.unop.toNCPMap z)
      = (f ≫ k).unop.toNCPMap z + (g ≫ k).unop.toNCPMap z
    rw [suop_comp_apply, suop_comp_apply]
  ovee_comp := fun {W X Y f g} h k => by
    have hadd : ∀ x y : X.unop.base.carrier,
        k.unop.toNCPMap (x + y) = k.unop.toNCPMap x + k.unop.toNCPMap y :=
      fun x y => map_add (ncpLin k.unop.toNCPMap) x y
    have hperp : (k ≫ f).unop.toNCPMap 1 + (k ≫ g).unop.toNCPMap 1 ≤ 1 := by
      rw [suop_comp_apply, suop_comp_apply, ← hadd]
      exact le_trans (ncpsu_mono k.unop h) k.unop.subunital'
    refine ⟨hperp, ?_⟩
    refine suop_hom_ext fun y => ?_
    rw [suop_comp_apply]
    show k.unop.toNCPMap (f.unop.toNCPMap y + g.unop.toNCPMap y)
      = (k ≫ f).unop.toNCPMap y + (k ≫ g).unop.toNCPMap y
    rw [hadd, suop_comp_apply, suop_comp_apply]
  comp_zero := fun {X Y Z} f => by
    refine suop_hom_ext fun z => ?_
    rw [suop_comp_apply]
    show f.unop.toNCPMap 0 = 0
    exact map_zero (ncpLin f.unop.toNCPMap)
  zero_comp := fun {X Y Z} f => by
    refine suop_hom_ext fun z => ?_
    rw [suop_comp_apply]
    rfl
  compatible_sum := fun {X Y} b => by
    have hp₁ : pproj₁ Y Y = (suCoprodIso Y Y).hom ≫ suPdesc (𝟙 Y) 0 := by
      refine coprod.hom_ext ?_ ?_
      · rw [show (pproj₁ Y Y) = coprod.desc (𝟙 Y) 0 from rfl, coprod.inl_desc,
          ← Category.assoc, suInl_coprodIso, suPinl_desc]
      · rw [show (pproj₁ Y Y) = coprod.desc (𝟙 Y) 0 from rfl, coprod.inr_desc,
          ← Category.assoc, suInr_coprodIso, suPinr_desc]
    have hp₂ : pproj₂ Y Y = (suCoprodIso Y Y).hom ≫ suPdesc 0 (𝟙 Y) := by
      refine coprod.hom_ext ?_ ?_
      · rw [show (pproj₂ Y Y) = coprod.desc 0 (𝟙 Y) from rfl, coprod.inl_desc,
          ← Category.assoc, suInl_coprodIso, suPinl_desc]
      · rw [show (pproj₂ Y Y) = coprod.desc 0 (𝟙 Y) from rfl, coprod.inr_desc,
          ← Category.assoc, suInr_coprodIso, suPinr_desc]
    have e₁ : (pproj₁ Y Y).unop.toNCPMap 1
        = (suCoprodIso Y Y).hom.unop.toNCPMap
            ((1 : Y.unop.base.carrier), (0 : Y.unop.base.carrier)) := by
      rw [hp₁, suop_comp_apply]
      congr 1
      refine Prod.ext ?_ ?_
      · exact su_id_apply 1
      · rfl
    have e₂ : (pproj₂ Y Y).unop.toNCPMap 1
        = (suCoprodIso Y Y).hom.unop.toNCPMap
            ((0 : Y.unop.base.carrier), (1 : Y.unop.base.carrier)) := by
      rw [hp₂, suop_comp_apply]
      congr 1
      refine Prod.ext ?_ ?_
      · rfl
      · exact su_id_apply 1
    show (b ≫ pproj₁ Y Y).unop.toNCPMap 1 + (b ≫ pproj₂ Y Y).unop.toNCPMap 1 ≤ 1
    rw [suop_comp_apply, suop_comp_apply, e₁, e₂]
    have hsum : (suCoprodIso Y Y).hom.unop.toNCPMap
          ((1 : Y.unop.base.carrier), (0 : Y.unop.base.carrier))
        + (suCoprodIso Y Y).hom.unop.toNCPMap
          ((0 : Y.unop.base.carrier), (1 : Y.unop.base.carrier))
        = (suCoprodIso Y Y).hom.unop.toNCPMap 1 := by
      refine (ncp_add_apply (suCoprodIso Y Y).hom.unop.toNCPMap
        ((1 : Y.unop.base.carrier), (0 : Y.unop.base.carrier))
        ((0 : Y.unop.base.carrier), (1 : Y.unop.base.carrier))).symm.trans ?_
      congr 1
      refine Prod.ext ?_ ?_
      · show (1 : Y.unop.base.carrier) + 0 = 1
        exact add_zero 1
      · show (0 : Y.unop.base.carrier) + 1 = 1
        exact zero_add 1
    have key : b.unop.toNCPMap ((suCoprodIso Y Y).hom.unop.toNCPMap
          ((1 : Y.unop.base.carrier), (0 : Y.unop.base.carrier)))
        + b.unop.toNCPMap ((suCoprodIso Y Y).hom.unop.toNCPMap
          ((0 : Y.unop.base.carrier), (1 : Y.unop.base.carrier)))
        = b.unop.toNCPMap ((suCoprodIso Y Y).hom.unop.toNCPMap 1) :=
      (ncp_add_apply b.unop.toNCPMap _ _).symm.trans
        (congrArg b.unop.toNCPMap hsum)
    refine le_trans (le_of_eq key) ?_
    exact le_trans (ncpsu_mono b.unop (suCoprodIso Y Y).hom.unop.subunital')
      b.unop.subunital'
  untying := fun {X Y f g} h => by
    show (f ≫ (coprod.inl : Y ⟶ Y ⨿ Y)).unop.toNCPMap 1
      + (g ≫ (coprod.inr : Y ⟶ Y ⨿ Y)).unop.toNCPMap 1 ≤ 1
    rw [suop_comp_apply, suop_comp_apply]
    exact le_trans (add_le_add
      (ncpsu_mono f.unop (coprod.inl : Y ⟶ Y ⨿ Y).unop.subunital')
      (ncpsu_mono g.unop (coprod.inr : Y ⟶ Y ⨿ Y).unop.subunital')) h

/-! ### The effects: `I = ℂ`, `Pred 𝒜 = [0,1]_𝒜` -/

attribute [local instance] suFinPAC

/-- The truth predicate `1 : 𝒜 ⟶ ℂ` of `vN_cpsuᵒᵖ`, i.e. the unit map
`z ↦ z·1` of `vN_cpsu`. -/
noncomputable def wUnitSU (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Theses.NCPSUMap (ULift.{u} ℂ) A :=
  ⟨(wUnit A).toNCPMap, le_of_eq (wUnit A).unital'⟩

@[simp] theorem wUnitSU_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (z : ULift.{u} ℂ) :
    (wUnitSU A).toNCPMap z = z.down • (1 : A) := rfl

/-- An ncpsu-map out of the scalars is `z ↦ z·f(1)`. -/
theorem ncpsu_scal_apply {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (f : Theses.NCPSUMap (ULift.{u} ℂ) A) (z : ULift.{u} ℂ) :
    f.toNCPMap z = z.down • f.toNCPMap 1 := by
  have hz : (z.down • (1 : ULift.{u} ℂ)) = z :=
    Theses.A.VN.CU.down_injective (by simp)
  conv_lhs => rw [← hz]
  exact ncp_smul_apply f.toNCPMap z.down 1

/-- The effect object of `vN_cpsuᵒᵖ`: the scalars. -/
noncomputable abbrev suI : WStarCPSU.{u}ᵒᵖ :=
  Opposite.op (WStarCPSU.of (WStar.of (ULift.{u} ℂ)))

/-- The truth predicate `1 : X ⟶ ℂ` as a morphism of `vN_cpsuᵒᵖ`. -/
noncomputable def suOne (X : WStarCPSU.{u}ᵒᵖ) : X ⟶ suI :=
  Quiver.Hom.op (wUnitSU X.unop.base.carrier)

theorem suOne_unop_one (X : WStarCPSU.{u}ᵒᵖ) :
    (suOne X).unop.toNCPMap 1 = (1 : X.unop.base.carrier) :=
  (wUnit X.unop.base.carrier).unital'

/-- **The effect structure of `vN_cpsuᵒᵖ`** (180VII.2): the effect object is
the scalars `ℂ`, so that `Pred 𝒜 = vN_cpsu(ℂ, 𝒜) ≅ [0,1]_𝒜`; the truth
predicate is the unit map and `p^⊥` is `1 - p`. -/
noncomputable def suEffectusPartialForm : EffectusPartialForm (WStarCPSU.{u}ᵒᵖ) where
  I := suI
  one X := suOne X
  orth {X} p := Quiver.Hom.op
    (wEffect (sub_nonneg.mpr p.unop.subunital')
      (sub_le_self 1 (ncpsu_one_nonneg p.unop)))
  perp_orth := fun {X} p => by
    show p.unop.toNCPMap 1
      + (1 : ULift.{u} ℂ).down • ((1 : X.unop.base.carrier) - p.unop.toNCPMap 1)
      ≤ 1
    have h1 : (1 : ULift.{u} ℂ).down • ((1 : X.unop.base.carrier)
        - p.unop.toNCPMap 1) = (1 : X.unop.base.carrier) - p.unop.toNCPMap 1 := by
      simp
    rw [h1]
    refine le_of_eq ?_
    abel
  ovee_orth := fun {X} p => by
    refine Quiver.Hom.unop_inj (ncpsu_ext fun z => ?_)
    show p.unop.toNCPMap z
      + z.down • ((1 : X.unop.base.carrier) - p.unop.toNCPMap 1)
      = z.down • (1 : X.unop.base.carrier)
    have hp : p.unop.toNCPMap z = z.down • p.unop.toNCPMap 1 :=
      ncpsu_scal_apply p.unop z
    rw [hp, ← smul_add]
    congr 1
    abel
  orth_unique := fun {X p q} h heq => by
    refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
    have hval : p.unop.toNCPMap 1 + q.unop.toNCPMap 1
        = (1 : X.unop.base.carrier) := by
      have h1 := congrArg (fun k : X ⟶ suI => k.unop.toNCPMap 1) heq
      exact h1.trans (suOne_unop_one X)
    show q.unop.toNCPMap 1
      = (1 : ULift.{u} ℂ).down • ((1 : X.unop.base.carrier) - p.unop.toNCPMap 1)
    have h2 : (1 : ULift.{u} ℂ).down • ((1 : X.unop.base.carrier)
        - p.unop.toNCPMap 1) = (1 : X.unop.base.carrier) - p.unop.toNCPMap 1 := by
      simp
    rw [h2, ← hval]
    abel
  eq_zero_of_perp_one := fun {X p} h => by
    refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
    have h1 : p.unop.toNCPMap 1 + (1 : X.unop.base.carrier) ≤ 1 := by
      refine le_trans (le_of_eq ?_) h
      exact congrArg (fun t => p.unop.toNCPMap 1 + t) (suOne_unop_one X).symm
    have h2 : p.unop.toNCPMap 1 ≤ 0 := by
      have h3 := sub_le_sub_right h1 (1 : X.unop.base.carrier)
      simpa using h3
    have h4 : p.unop.toNCPMap 1 = 0 :=
      le_antisymm h2 (ncpsu_one_nonneg p.unop)
    exact h4.trans rfl
  perp_of_one_perp := fun {X Y f g} h => by
    have hf : (f ≫ suOne Y).unop.toNCPMap 1 = f.unop.toNCPMap 1 := by
      rw [suop_comp_apply]
      exact congrArg f.unop.toNCPMap (suOne_unop_one Y)
    have hg : (g ≫ suOne Y).unop.toNCPMap 1 = g.unop.toNCPMap 1 := by
      rw [suop_comp_apply]
      exact congrArg g.unop.toNCPMap (suOne_unop_one Y)
    show f.unop.toNCPMap 1 + g.unop.toNCPMap 1 ≤ 1
    rw [← hf, ← hg]
    exact h
  eq_zero_of_one_zero := fun {X Y f} h => by
    refine Quiver.Hom.unop_inj (ncpsu_ext fun y => ?_)
    have h1 := congrArg (fun k : X ⟶ suI => k.unop.toNCPMap 1) h
    rw [suop_comp_apply] at h1
    have h2 : f.unop.toNCPMap 1 = 0 := by
      refine Eq.trans ?_ h1
      exact congrArg f.unop.toNCPMap (suOne_unop_one Y).symm
    exact ncp_eq_zero_of_one f.unop.toNCPMap h2 y

end SUCat

end VNPartial

/-- The partial-form effectus structure `vN_cpsuᵒᵖ` carries, bundled: the
concrete finite coproducts, PCM-enrichment, finPAC axioms and effects data
built above.  (`effectus_vn_partial` is its existential form; the bundled
version is what `vn_effObj_iso` compares an arbitrary structure with.) -/
noncomputable def vnPartialStructure : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ :=
  { hasFiniteCoproducts := suHasFiniteCoproducts
    homPCM := suPCM
    finPAC := suFinPAC
    effectus := suEffectusPartialForm }

/-- **180V** (`effectus-vn`, eff.tex:827): `(W*_ncpsu)ᵒᵖ` is an effectus in
**partial form**.

The **effect object is pinned to `ℂᵤ`**, matching `cho_thm_1`
(`Effectus.lean`, which asserts `s.effectus.I = Par.of (⊤_ C)`): the
statement is `∃ s, s.effectus.I = suI`, which is what `suEffectusPartialForm`
builds anyway.  This was `docs/DECISIONS.md` §2.7 (and QUESTIONS **B13**, now
closed, deleted 2026-09-04), **ruled option (a) by the author on 2026-09-04**:
pin the effect object.  Before that ruling the
statement was the weaker `Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ)`,
which says only that *some* structure exists.  What the eight examples
downstream actually use is neither, but the *uniqueness* statement
`vn_effObj_iso`.

⚠ **What this statement still does not say** (audit row 180V).  The
sentence of 180V being rendered is *"the partial maps \[of `vNᵒᵖ`\]
correspond to ncp-maps `f` with `f(1) ≤ 1`"*, i.e. `Par(vNᵒᵖ) ≃ W*_ncpsuᵒᵖ`.
One clause of it is **not** in the statement below:

* **the comparison with `Par(vNᵒᵖ)` itself.**  Nothing here relates
  `W*_ncpsuᵒᵖ` to the category of partial maps of the *total*-form effectus
  `effectus_vn`.  This is the blocker for four
  `StatesPredicates` rows: `Par C` needs `HasFiniteCoproducts C` and
  `HasTerminal C` as **instances**, and for `WStarNCPU.{u}ᵒᵖ` those live
  inside the proof of `effectus_vn` as a `CoprodPres` record (`vnPres`), so
  the statement would first have to hoist them and then transport along
  `⊤_ C ≅ vnPres.T` and `Y ⨿ ⊤_ C ≅ vnPres.P Y vnPres.T` before the
  hom-bijection `φ ↦ φ(·, 0)` (inverse `f ↦ ((y, λ) ↦ f(y) + λ(1 - f(1)))`)
  and its compatibility with Kleisli composition could even be stated. -/

theorem effectus_vn_partial :
    ∃ s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ, s.effectus.I = suI :=
  ⟨vnPartialStructure, rfl⟩

/-! ## Uniqueness of the effect object of `vN_cpsuᵒᵖ`

The eight hypothetical examples below each quantify over an **arbitrary**
`s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ`, so none of them may use
`effectus_vn_partial`; what they need instead is that such an `s` is
essentially unique.  Three of its four fields already are:
`hasFiniteCoproducts` and `finPAC` are `Prop`s, and `homPCM` is
`effectusPartialStructure_homPCM_unique` (`Comparisons.lean`).  The one free
datum is the **effect object** `I`, and `vn_effObj_iso` below pins it: for
any `s`, `s.effectus.I ≅ ℂᵤ`, compatibly with the truth predicates.

Note that the effect *structure* on top of `I` is then determined too:
`orth` by `orth_unique` and `one X` as the `≼`-greatest predicate — which is
how the argument proceeds.  Writing `A` for the algebra underlying
`s.effectus.I` and `φ = 1_{ℂᵤ}` for the truth predicate at `ℂᵤ` (an ncpsu
functional `A → ℂᵤ`), the steps are:

1. `p ⋁ pᗮ = 1` is the *pointwise* sum, so every predicate is dominated
   pointwise by the truth predicate (`su_pred_le_truth'`).
2. `A` is not the trivial algebra (`su_effCarrier_one_ne_zero`), else
   `1 = 0` in `ℂ` by `eq_zero_of_one_zero` at `𝟙 ℂᵤ`.
3. Hence `A` carries a normal state, i.e. a *unital* ncpsu-map `ψ : A → ℂᵤ`
   (`exists_ncpsu_state`, from the faithfulness axiom of
   `Theses.VonNeumannAlgebra` at `1`, normalised).  Since `ψ ≤ φ` pointwise
   and `φ 1 ≤ 1 = ψ 1`, the orthocomplement of `ψ` kills `1`, hence is `0`:
   `φ = ψ`, and in particular `φ 1 = 1`.
4. **`1_I = 𝟙 I`** (`one_m_is_id`, 181XIII) says the identity is the greatest
   element of `vN_cpsu(A, A)`, so `φ(a)·1 ≤ a` for every `a ≥ 0`.  Applying
   that to `a` and to `‖a‖·1 − a` at once gives `φ(a)·1 ≤ a ≤ φ(a)·1`, so
   every positive `a` — hence, by `linear_eq_zero_of_nonneg`, every `a` — is
   the scalar `φ(a)·1`.  That is exactly `A ≅ ℂ`, and `φ` and the unit map
   are mutually inverse.
5. Finally `1_X(1) = 1` for every `X`, because `a ↦ φ(a)·1_X` is a *unital*
   predicate dominated by `1_X`; that is the compatibility clause, and it
   yields `su_isTotal_iff`: **the total maps of any such `s` are exactly the
   ncpu-maps**.

Step 4 is what avoids the circle "`I` terminal in `Tot`".  The tempting
`I`-free way round it — the characterisation *total ⟺ `≼`-maximal* — is
**false** in `vN_cpsuᵒᵖ`: the unique map `X ⟶ 0` into the initial object is
`≼`-maximal but not total unless `X` is a zero object.  Step 4 instead uses
`one_m_is_id` at the effect object itself and never mentions `Tot`. -/

section StateExists

open Theses.A.CStar
open scoped ComplexOrder ComplexStarModule

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `ULift.up : ℂ → ℂᵤ` as a linear map. -/
private noncomputable def cuUpLin : ℂ →ₗ[ℂ] ULift.{u} ℂ where
  toFun := ULift.up
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem isLUB_up {S : Set ℂ} {x : ℂ} (h : IsLUB S x) :
    IsLUB ((fun z : ℂ => (ULift.up z : ULift.{u} ℂ)) '' S) (ULift.up x) := by
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    exact h.1 hz
  · intro b hb
    exact h.2 (fun z hz => hb ⟨z, hz, rfl⟩)

/-- An np-functional as an ncp-map into the lifted scalars. -/
private noncomputable def npNCP (ω : Theses.NPFunctional A) :
    Theses.NCPMap A (ULift.{u} ℂ) :=
  mkNCP (cuUpLin.comp (ω.toPositiveLinearMap : A →ₗ[ℂ] ℂ))
    (cp_comp _ _ (cp_commutative_cod _ (fun a ha => Theses.A.VN.npFunctional_nonneg ω ha))
      (cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl)))
    (by
      intro D s hne hdir hlub
      have h2 := isLUB_up.{u} (ω.preservesDirSups' D s hne hdir hlub)
      rw [Set.image_image] at h2
      exact h2)

@[simp] private theorem npNCP_apply (ω : Theses.NPFunctional A) (a : A) :
    (npNCP ω) a = ULift.up (ω a) := rfl

/-- Scaling by a nonnegative real is monotone for the C\*-order. -/
theorem smul_le_smul_cstar {r : ℝ} (hr : 0 ≤ r) {x y : A} (h : x ≤ y) :
    ((r : ℂ)) • x ≤ ((r : ℂ)) • y := by
  have h0 : (0 : A) ≤ ((r : ℂ)) • (y - x) :=
    cstar_positive_1 _ (sub_nonneg.mpr h) r hr
  rw [smul_sub] at h0
  exact sub_nonneg.mp h0

/-- `t·1 ≤ 1` for a real `t ∈ [0,1]`. -/
theorem smul_one_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((t : ℂ)) • (1 : A) ≤ (1 : A) := by
  have h : (0 : A) ≤ (((1 - t : ℝ)) : ℂ) • (1 : A) :=
    cstar_positive_1 1 zero_le_one _ (by linarith)
  rw [show (((1 - t : ℝ)) : ℂ) = 1 - (t : ℂ) by push_cast; ring, sub_smul,
    one_smul] at h
  exact sub_nonneg.mp h

/-- **Every np-functional with `ω 1 ≠ 0` normalises to a normal state**: a
*unital* ncpsu-map `ψ : A → ℂᵤ` with `ω = ω(1)·ψ`. -/
theorem exists_ncpsu_state_of_np (ω : Theses.NPFunctional A) (hω : ω 1 ≠ 0) :
    ∃ ψ : Theses.NCPSUMap A (ULift.{u} ℂ), ψ.toNCPMap 1 = 1 ∧
      ∀ a : A, ω a = ω 1 * (ψ.toNCPMap a).down := by
  have hpos : (0 : ℂ) ≤ ω 1 := Theses.A.VN.npFunctional_nonneg ω zero_le_one
  obtain ⟨hre, him⟩ := Complex.le_def.mp hpos
  obtain ⟨c, hc, hcpos⟩ : ∃ c : ℝ, ((c : ℂ) = ω 1 ∧ 0 < c) := by
    refine ⟨(ω 1).re, ?_, ?_⟩
    · refine Complex.ext (by simp) ?_
      simpa using him
    · rcases lt_or_eq_of_le (by simpa using hre) with h | h
      · exact h
      · exact absurd (by refine Complex.ext (by simpa using h.symm) (by simpa using him.symm)) hω
  have hc0 : (c : ℂ) ≠ 0 := by
    simpa using hcpos.ne'
  have hnn : (0 : ULift.{u} ℂ) ≤ ((c⁻¹ : ℝ) : ℂ) • (1 : ULift.{u} ℂ) :=
    cstar_positive_1 1 zero_le_one _ (le_of_lt (inv_pos.mpr hcpos))
  have hval : ((ncpLin (Theses.A.VN.ncpOfNonneg hnn)).comp (ncpLin (npNCP ω))) 1
      = (1 : ULift.{u} ℂ) := by
    refine Theses.A.VN.CU.down_injective ?_
    show (ω 1) * (((c⁻¹ : ℝ) : ℂ) * 1) = 1
    rw [mul_one, ← hc]
    push_cast
    field_simp
  obtain ⟨ψ, hψd⟩ : ∃ ψ : Theses.NCPSUMap A (ULift.{u} ℂ),
      ∀ a : A, (ψ.toNCPMap a).down = (ω a) * (((c⁻¹ : ℝ) : ℂ) * 1) :=
    ⟨mkNCPSU ((ncpLin (Theses.A.VN.ncpOfNonneg hnn)).comp (ncpLin (npNCP ω)))
      (cp_comp _ _ (ncpLin_cp _) (ncpLin_cp _))
      (preservesDirSups_comp' (f := ⇑(ncpLin (npNCP ω)))
        (g := ⇑(ncpLin (Theses.A.VN.ncpOfNonneg hnn)))
        (ncpLin_normal (npNCP ω))
        (fun a => sa_of_cp (ncpLin_cp (npNCP ω)) a.2) (ncpLin_normal _))
      (le_of_eq hval), fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_⟩
  · refine Theses.A.VN.CU.down_injective ?_
    rw [hψd 1, Theses.A.VN.CU.down_one, mul_one, ← hc]
    push_cast
    field_simp
  · intro a
    rw [hψd a, mul_one, ← hc]
    push_cast
    field_simp

/-- **Every nontrivial von Neumann algebra carries a normal state**, here in
the form needed for the effectus argument: a *unital* ncpsu-map `A → ℂᵤ`.
(An np-functional exists by the faithfulness axiom of
`Theses.VonNeumannAlgebra` applied to `1`; it is then normalised by
composing with `z ↦ z·ω(1)⁻¹`.) -/
theorem exists_ncpsu_state (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] (h1 : (1 : A) ≠ 0) :
    ∃ ψ : Theses.NCPSUMap A (ULift.{u} ℂ), ψ.toNCPMap 1 = 1 := by
  obtain ⟨ω, hω⟩ : ∃ ω : Theses.NPFunctional A, ω 1 ≠ 0 := by
    by_contra h
    exact h1 (Theses.VonNeumannAlgebra.np_faithful 1 zero_le_one
      (fun ω => not_not.mp fun hne => h ⟨ω, hne⟩))
  obtain ⟨ψ, hψ, -⟩ := exists_ncpsu_state_of_np ω hω
  exact ⟨ψ, hψ⟩

/-- **Normal states separate the elements of a von Neumann algebra.**  The
faithfulness axiom of `Theses.VonNeumannAlgebra` gives this for *positive*
elements only; the extension to self-adjoint ones is by conjugation:
`ω(y⁺ · y⁺)` is again an np-functional (`conjNP`), and it turns `y` into the
positive element `(y⁺)³`, because `y⁺y⁻ = 0`.  (Supplied here: 190III is
asserted in eff.tex without proof.) -/
theorem eq_zero_of_ncpsu_states (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] {y : A}
    (hy : IsSelfAdjoint y)
    (hst : ∀ ψ : Theses.NCPSUMap A (ULift.{u} ℂ), ψ.toNCPMap 1 = 1 →
      ψ.toNCPMap y = 0) : y = 0 := by
  -- (1) every np-functional kills `y`
  have hnp : ∀ ω : Theses.NPFunctional A, ω y = 0 := by
    intro ω
    by_cases hω : ω 1 = 0
    · have h0 : (npNCP ω) (1 : A) = 0 := by
        rw [npNCP_apply, hω]; rfl
      have h := ncp_eq_zero_of_one (npNCP ω) h0 y
      rw [npNCP_apply] at h
      exact congrArg ULift.down h
    · obtain ⟨ψ, hψ1, hψ⟩ := exists_ncpsu_state_of_np ω hω
      rw [hψ y, hst ψ hψ1]
      simp
  -- (2) a positive element with `b³ = 0` is zero
  have cube_zero : ∀ b : A, IsSelfAdjoint b → b * b * b = 0 → b = 0 := by
    intro b hb h3
    have hsa2 : star (b * b) = b * b := by rw [star_mul, hb.star_eq]
    have h4 : star (b * b) * (b * b) = 0 := by
      rw [hsa2, ← mul_assoc, h3, zero_mul]
    have h2 : b * b = 0 := by
      have hn := CStarRing.norm_star_mul_self (x := b * b)
      rw [h4, norm_zero] at hn
      exact norm_eq_zero.mp (mul_self_eq_zero.mp hn.symm)
    have hn := CStarRing.norm_star_mul_self (x := b)
    rw [hb.star_eq, h2, norm_zero] at hn
    exact norm_eq_zero.mp (mul_self_eq_zero.mp hn.symm)
  have hsplit : posPart y - negPart y = y := CFC.posPart_sub_negPart y hy
  have hpn : posPart y * negPart y = 0 := CFC.posPart_mul_negPart y
  have hnpm : negPart y * posPart y = 0 := CFC.negPart_mul_posPart y
  have hp0 : (0 : A) ≤ posPart y := CFC.posPart_nonneg y
  have hn0 : (0 : A) ≤ negPart y := CFC.negPart_nonneg y
  have hpsa : IsSelfAdjoint (posPart y) := hp0.isSelfAdjoint
  have hnsa : IsSelfAdjoint (negPart y) := hn0.isSelfAdjoint
  -- (3) the positive part
  have hpz : posPart y = 0 := by
    refine cube_zero _ hpsa (Theses.VonNeumannAlgebra.np_faithful _ ?_ ?_)
    · have h := star_left_conjugate_le_conjugate hp0 (posPart y)
      rwa [mul_zero, zero_mul, hpsa.star_eq] at h
    · intro ω
      have hcube : posPart y * (posPart y - negPart y) * posPart y
          = posPart y * posPart y * posPart y := by
        rw [mul_sub, sub_mul, hpn, zero_mul, sub_zero]
      rw [hsplit] at hcube
      have h := hnp (Theses.A.VN.conjNP (posPart y) ω)
      rw [Theses.A.VN.conjNP_apply, hpsa.star_eq, hcube] at h
      exact h
  -- (4) the negative part
  have hnz : negPart y = 0 := by
    refine cube_zero _ hnsa (Theses.VonNeumannAlgebra.np_faithful _ ?_ ?_)
    · have h := star_left_conjugate_le_conjugate hn0 (negPart y)
      rwa [mul_zero, zero_mul, hnsa.star_eq] at h
    · intro ω
      have hcube : negPart y * (posPart y - negPart y) * negPart y
          = -(negPart y * negPart y * negPart y) := by
        rw [mul_sub, sub_mul, hnpm, zero_mul, zero_sub]
      rw [hsplit] at hcube
      have h := hnp (Theses.A.VN.conjNP (negPart y) ω)
      rw [Theses.A.VN.conjNP_apply, hnsa.star_eq, hcube] at h
      have hlin : ω (-(negPart y * negPart y * negPart y))
          = -(ω (negPart y * negPart y * negPart y)) :=
        map_neg ω.toPositiveLinearMap _
      rw [hlin] at h
      exact neg_eq_zero.mp h
  rw [hpz, hnz, sub_zero] at hsplit
  exact hsplit.symm

end StateExists



/-! ## Rank-one projections, and `B(ℋ)` as a factor (infrastructure for 224VII)

The one genuinely operator-theoretic input of **224VII** is the step where
`bsols.tex` concludes, from `⌈ξ(1)⌉p_𝒮⌈ξ(1)⌉` being central in
`⌈ξ(1)⌉M₄⌈ξ(1)⌉`, that it is `0` or `⌈ξ(1)⌉` — i.e. that a corner of a
factor is a factor.  It enters the argument only through the following
form of the conclusion:

> if a projection `p` commutes with `s x s` for every effect `x` of `B(ℋ)`,
> then `p s = 0` or `p s = s`   (`proj_mul_selfAdjoint`).

Testing the hypothesis against the *rank-one* effects `|ξ⟩⟨ξ|` gives
`⟪sξ,sξ⟫ · p(sξ) = ⟪sξ,p(sξ)⟫ · sξ`, whence `p(sξ) ∈ {0, sξ}` for every
`ξ`; and a vector space is not the union of two proper subspaces.  This
route needs neither the pseudoinverse of `√ξ(1)` nor factoriality as such. -/

section RankOne

open scoped ComplexInnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The rank-one operator `|ξ⟩⟨ξ| : ζ ↦ ⟪ξ,ζ⟫ ξ` on a Hilbert space. -/
noncomputable def rk1 (ξ : H) : H →L[ℂ] H := (innerSL ℂ ξ).smulRight ξ

omit [CompleteSpace H] in
theorem rk1_apply (ξ x : H) : rk1 ξ x = (⟪ξ, x⟫ : ℂ) • ξ := rfl

theorem rk1_star (ξ : H) : star (rk1 ξ) = rk1 ξ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_).symm
  intro x y
  simp only [rk1_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-- `|ξ⟩⟨ξ|` is a projection for a unit vector `ξ`. -/
theorem rk1_isStarProjection {ξ : H} (h : ‖ξ‖ = 1) :
    IsStarProjection (rk1 ξ) := by
  refine ⟨?_, rk1_star ξ⟩
  ext x
  simp [rk1_apply, h]

/-- **The factoriality input of 224VII.**  If a projection `p` of `B(ℋ)`
commutes with `s x s` for every effect `x`, then `p s = 0` or `p s = s`. -/
theorem proj_mul_selfAdjoint {s p : H →L[ℂ] H} (hs : IsSelfAdjoint s)
    (hp : IsStarProjection p)
    (hcomm : ∀ x : H →L[ℂ] H, 0 ≤ x → x ≤ 1 →
      p * (s * x * s) = s * x * s * p) :
    p * s = 0 ∨ p * s = s := by
  have hsym : ∀ x y : H, (⟪s x, y⟫ : ℂ) = ⟪x, s y⟫ :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs)
  have hpp : ∀ v : H, p (p v) = p v := by
    intro v
    have h := hp.isIdempotentElem.eq
    calc p (p v) = (p * p) v := rfl
      _ = p v := by rw [h]
  -- the pointwise dichotomy, tested against `|ξ⟩⟨ξ|`
  have key : ∀ ξ : H, p (s ξ) = 0 ∨ p (s ξ) = s ξ := by
    have unit : ∀ ξ : H, ‖ξ‖ = 1 → (p (s ξ) = 0 ∨ p (s ξ) = s ξ) := by
      intro ξ hξ
      have hpr := rk1_isStarProjection hξ
      have h := hcomm (rk1 ξ) hpr.nonneg hpr.le_one
      have happ := congrArg (fun T : H →L[ℂ] H => T (s ξ)) h
      simp only [ContinuousLinearMap.mul_apply, rk1_apply,
        ContinuousLinearMap.map_smul] at happ
      set c : ℂ := (⟪s ξ, s ξ⟫ : ℂ) with hc
      set d : ℂ := (⟪s ξ, p (s ξ)⟫ : ℂ) with hd
      have e1 : c • p (s ξ) = d • s ξ := by
        rw [hc, hd, hsym, hsym]; exact happ
      have e2 : c • p (s ξ) = d • p (s ξ) := by
        have h2 := congrArg (fun v : H => p v) e1
        simpa [hpp] using h2
      by_cases hd0 : d = 0
      · left
        rw [hd0, zero_smul] at e1
        by_cases hc0 : c = 0
        · have hz : s ξ = 0 := inner_self_eq_zero.mp hc0
          rw [hz, map_zero]
        · exact (smul_eq_zero.mp e1).resolve_left hc0
      · right
        have h3 : d • s ξ = d • p (s ξ) := by rw [← e1, e2]
        exact (smul_right_injective H hd0 h3).symm
    intro ξ
    by_cases hξ : ξ = 0
    · left; rw [hξ, map_zero, map_zero]
    · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
      set r : ℂ := (‖ξ‖ : ℂ)⁻¹ with hr
      have hr0 : r ≠ 0 := by simp [hr, hn]
      have hnr : ‖r • ξ‖ = 1 := by
        rw [norm_smul, hr]; simp [hn]
      rcases unit (r • ξ) hnr with h | h
      · left
        rw [map_smul, map_smul] at h
        exact (smul_eq_zero.mp h).resolve_left hr0
      · right
        rw [map_smul, map_smul] at h
        exact smul_right_injective H hr0 h
  -- a vector space is not the union of two proper subspaces
  have dich : (∀ ξ : H, p (s ξ) = 0) ∨ (∀ ξ : H, p (s ξ) = s ξ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨ξ₁, h₁⟩, ⟨ξ₂, h₂⟩⟩ := hcon
    have e₁ : p (s ξ₁) = s ξ₁ := (key ξ₁).resolve_left h₁
    have e₂ : p (s ξ₂) = 0 := (key ξ₂).resolve_right h₂
    have hs₂ : s ξ₂ ≠ 0 := fun h => h₂ (by rw [e₂, h])
    have hs₁ : s ξ₁ ≠ 0 := fun h => h₁ (by rw [e₁, h])
    have esum : p (s (ξ₁ + ξ₂)) = s ξ₁ := by
      rw [map_add, map_add, e₁, e₂, add_zero]
    rcases key (ξ₁ + ξ₂) with h | h
    · exact hs₁ (by rw [← esum, h])
    · rw [esum, map_add] at h
      refine hs₂ ?_
      have h4 := h.symm
      rwa [add_eq_left] at h4
  rcases dich with h | h
  · left; ext v; simpa using h v
  · right; ext v; simpa using h v

end RankOne

/-! ## States and the square root (infrastructure for 224VI)

The step of **224VI** that replaces the printed solution's GNS analysis is
`su_state_sqrtConj`: a *state* `ω` with `ω(a) = 1` satisfies
`ω(√a x √a) = ω(x)` for every `x`.  (For a vector state `⟨v, ·v⟩` this says
`a v = v ⟹ √a v = v`.)  It rests on Cauchy–Schwarz for positive
functionals, **30IV**.1 (`omega-norm-basic`, cstar.tex:4787)
`omega_norm_basic_1`. -/

section StateSqrt

open Theses.A.CStar
open scoped ComplexOrder

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ≤ √a` for an effect `a` (conjugate `√a ≤ 1` by `⁴√a`). -/
theorem su_le_sqrt {a : A} (h0 : 0 ≤ a) (h1 : a ≤ 1) : a ≤ CFC.sqrt a := by
  have hs0 : (0 : A) ≤ CFC.sqrt a := CFC.sqrt_nonneg a
  have hs1 : CFC.sqrt a ≤ 1 := by simpa using CFC.sqrt_le_sqrt a 1 h1
  set c : A := CFC.sqrt (CFC.sqrt a) with hc
  have hc0 : (0 : A) ≤ c := CFC.sqrt_nonneg _
  have hcc : c * c = CFC.sqrt a := CFC.sqrt_mul_sqrt_self _ hs0
  have key := (IsSelfAdjoint.of_nonneg hc0).conjugate_le_conjugate hs1
  have e1 : c * CFC.sqrt a * c = a := by
    rw [← hcc]
    have h : c * (c * c) * c = c * c * (c * c) := by noncomm_ring
    rw [h, hcc, CFC.sqrt_mul_sqrt_self a h0]
  have e2 : c * 1 * c = CFC.sqrt a := by rw [mul_one, hcc]
  rwa [e1, e2] at key

/-- `d² ≤ d` for an effect `d`. -/
theorem su_sq_le_self {d : A} (h0 : 0 ≤ d) (h1 : d ≤ 1) : d * d ≤ d := by
  set s : A := CFC.sqrt d with hs
  have hs0 : (0 : A) ≤ s := CFC.sqrt_nonneg d
  have hss : s * s = d := CFC.sqrt_mul_sqrt_self d h0
  have key := (IsSelfAdjoint.of_nonneg hs0).conjugate_le_conjugate h1
  have e1 : s * d * s = d * d := by rw [← hss]; noncomm_ring
  have e2 : s * 1 * s = d := by rw [mul_one, hss]
  rwa [e1, e2] at key

/-- A corollary of **Cauchy–Schwarz** for positive functionals
(**30IV**.1, `omega-norm-basic`, cstar.tex:4787, `omega_norm_basic_1`): a
positive functional killing an effect `d` kills every product with `d`.
This is a consequence of 30IV.1, not a transcription of it. -/
theorem su_posFun_mul_eq_zero (ω : A →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω) {d : A}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (h0 : ω d = 0) :
    (∀ b : A, ω (d * b) = 0) ∧ (∀ b : A, ω (b * d) = 0) := by
  have hds : star d = d := (IsSelfAdjoint.of_nonneg hd0).star_eq
  have hmono : ∀ x y : A, x ≤ y → ω x ≤ ω y := by
    intro x y hxy
    have h := hω (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  have hdd0 : ω (star d * d) = 0 := by
    rw [hds]
    have hnn : (0 : A) ≤ d * d := by
      have h := star_mul_self_nonneg d
      rwa [hds] at h
    refine le_antisymm ?_ (hω _ hnn)
    rw [← h0]
    exact hmono _ _ (su_sq_le_self hd0 hd1)
  have hzero : ∀ z : A, ((‖ω z‖ : ℂ)) ^ 2 ≤ 0 → ω z = 0 := by
    intro z hz
    have hle : ((‖ω z‖ ^ 2 : ℝ) : ℂ) ≤ 0 := by push_cast; exact hz
    have h2 : (‖ω z‖ : ℝ) ^ 2 ≤ 0 := by
      exact_mod_cast Complex.real_le_real.mp (by simpa using hle)
    have h3 : ‖ω z‖ = 0 := by nlinarith [norm_nonneg (ω z)]
    exact norm_eq_zero.mp h3
  constructor
  · intro b
    have hcs := omega_norm_basic_1 ω hω d b
    rw [hdd0, zero_mul] at hcs
    have h := hzero _ hcs
    rwa [hds] at h
  · intro b
    have hcs := omega_norm_basic_1 ω hω (star b) d
    rw [star_star, hdd0, mul_zero] at hcs
    exact hzero _ hcs

/-- **A state fixing an effect `a` is invariant under `x ↦ √a x √a`.** -/
theorem su_state_sqrtConj (ω : A →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω) (hu : ω 1 = 1)
    {a : A} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hfix : ω a = 1) (x : A) :
    ω (CFC.sqrt a * x * CFC.sqrt a) = ω x := by
  have hmono : ∀ x y : A, x ≤ y → ω x ≤ ω y := by
    intro x y hxy
    have h := hω (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  set s : A := CFC.sqrt a with hs
  have hs0 : (0 : A) ≤ s := CFC.sqrt_nonneg a
  have hs1 : s ≤ 1 := by rw [hs]; simpa using CFC.sqrt_le_sqrt a 1 ha1
  have hωs : ω s = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hu]; exact hmono _ _ hs1
    · rw [← hfix]; exact hmono _ _ (hs ▸ su_le_sqrt ha0 ha1)
  set d : A := 1 - s with hd
  have hd0 : (0 : A) ≤ d := sub_nonneg.mpr hs1
  have hd1 : d ≤ 1 := by rw [hd]; simpa using hs0
  have hωd : ω d = 0 := by rw [hd, map_sub, hu, hωs, sub_self]
  obtain ⟨hL, hR⟩ := su_posFun_mul_eq_zero ω hω hd0 hd1 hωd
  have hid : x - s * x * s = d * x + s * x * d := by rw [hd]; noncomm_ring
  have h := congrArg ω hid
  rw [map_sub, map_add, hL x, hR (s * x), add_zero] at h
  exact (sub_eq_zero.mp h).symm

end StateSqrt

section IUnique

open Theses.A.CStar
open scoped ComplexOrder ComplexStarModule

attribute [local instance] suHasFiniteCoproducts suPCM suFinPAC

variable [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)]

/-- The von Neumann algebra underlying the effect object. -/
private abbrev effCarrier : Type u :=
  (effObj (WStarCPSU.{u}ᵒᵖ)).unop.base.carrier

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
private theorem ncpsu_nonneg {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : Theses.NCPSUMap A B) {a : A} (ha : 0 ≤ a) : 0 ≤ f.toNCPMap a := by
  have h := ncpsu_mono f ha
  rwa [ncp_zero_apply] at h

/-- The concrete form of `p ⋁ pᗮ = 1`: pointwise sum. -/
private theorem su_pred_ovee (X : WStarCPSU.{u}ᵒᵖ)
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (a : effCarrier) :
    p.unop.toNCPMap a + (EffectusPartialForm.orth p).unop.toNCPMap a
      = (truth X).unop.toNCPMap a :=
  congrArg (fun k : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ) => k.unop.toNCPMap a)
    (EffectusPartialForm.ovee_orth p)

/-- Every predicate is dominated by the truth predicate, pointwise. -/
private theorem su_pred_le_truth' (X : WStarCPSU.{u}ᵒᵖ)
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) {a : effCarrier} (ha : 0 ≤ a) :
    p.unop.toNCPMap a ≤ (truth X).unop.toNCPMap a := by
  rw [← su_pred_ovee X p a]
  exact le_add_of_nonneg_right (ncpsu_nonneg _ ha)

/-- The effect object is not the trivial algebra. -/
private theorem su_effCarrier_one_ne_zero : (1 : effCarrier) ≠ 0 := by
  intro h
  have : Subsingleton (effCarrier.{u}) := subsingleton_of_zero_eq_one h.symm
  have hz : truth (suI.{u}) = (0 : suI.{u} ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) := by
    refine suop_hom_ext fun a => ?_
    rw [Subsingleton.elim a 0, ncp_zero_apply]
    rfl
  have hid : (𝟙 suI.{u} : suI.{u} ⟶ suI.{u}) = 0 :=
    EffectusPartialForm.eq_zero_of_one_zero (by rw [Category.id_comp]; exact hz)
  have h1 := congrArg (fun k : suI.{u} ⟶ suI.{u} => k.unop.toNCPMap (1 : ULift.{u} ℂ)) hid
  have e1 : (𝟙 suI.{u} : suI.{u} ⟶ suI.{u}).unop.toNCPMap (1 : ULift.{u} ℂ) = 1 :=
    su_id_apply (X := suI.{u}.unop) 1
  exact one_ne_zero (α := ℂ) (congrArg ULift.down (e1.symm.trans h1))

/-- **Uniqueness of the effect object of `vN_cpsuᵒᵖ`**: the effect object of
*any* partial-form effectus structure on `vN_cpsuᵒᵖ` is isomorphic to the
scalars `ℂᵤ`, compatibly with the truth predicates. -/
theorem su_effObj_iso :
    ∃ θ : effObj (WStarCPSU.{u}ᵒᵖ) ≅ suI.{u},
      ∀ X : WStarCPSU.{u}ᵒᵖ, truth X ≫ θ.hom = suOne X := by
  obtain ⟨ψ, hψ⟩ := exists_ncpsu_state (effCarrier.{u}) su_effCarrier_one_ne_zero
  obtain ⟨p, hp⟩ : ∃ p : suI.{u} ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
      ∀ a : effCarrier, p.unop.toNCPMap a = ψ.toNCPMap a :=
    ⟨Quiver.Hom.op ψ, fun _ => rfl⟩
  -- the truth predicate on `ℂᵤ`, as an ncpsu functional on the effect algebra
  have hψ' : ψ.toNCPMap (1 : effCarrier)
      = (1 : (Opposite.unop (suI.{u})).base.carrier) := hψ
  have hsum1 := su_pred_ovee suI.{u} p 1
  rw [hp 1, hψ'] at hsum1
  have hr0 : (EffectusPartialForm.orth p).unop.toNCPMap (1 : effCarrier) = 0 := by
    refine le_antisymm ?_ (ncpsu_nonneg _ zero_le_one)
    have hle := le_trans (le_of_eq hsum1) (truth (suI.{u})).unop.subunital'
    have h6 := sub_le_sub_right hle 1
    rw [add_sub_cancel_left, sub_self] at h6
    exact h6
  have hφψ : ∀ a : effCarrier,
      (truth (suI.{u})).unop.toNCPMap a = ψ.toNCPMap a := by
    intro a
    rw [← su_pred_ovee suI.{u} p a, ncp_eq_zero_of_one _ hr0 a, add_zero, hp a]
  have hφ1 : (truth (suI.{u})).unop.toNCPMap (1 : effCarrier) = 1 := by
    rw [hφψ 1]; exact hψ'
  -- the ncpsu map `a ↦ φ(a)·1` of the effect algebra
  have hk : ∀ a : effCarrier,
      (suOne (effObj (WStarCPSU.{u}ᵒᵖ)) ≫ truth (suI.{u})).unop.toNCPMap a
        = ((truth (suI.{u})).unop.toNCPMap a).down • (1 : effCarrier) := fun a =>
    suop_comp_apply _ _ a
  have htruthEI : ∀ a : effCarrier,
      (truth (effObj (WStarCPSU.{u}ᵒᵖ))).unop.toNCPMap a = a := by
    intro a
    rw [one_m_is_id]
    exact su_id_apply a
  have hdom : ∀ a : effCarrier, 0 ≤ a →
      ((truth (suI.{u})).unop.toNCPMap a).down • (1 : effCarrier) ≤ a := by
    intro a ha
    have h := su_pred_le_truth' (effObj (WStarCPSU.{u}ᵒᵖ))
      (suOne (effObj (WStarCPSU.{u}ᵒᵖ)) ≫ truth (suI.{u})) ha
    rw [hk a, htruthEI a] at h
    exact h
  -- every positive element of the effect algebra is a scalar
  have hnorm : ∀ a : effCarrier, 0 ≤ a →
      a = ((truth (suI.{u})).unop.toNCPMap a).down • (1 : effCarrier) := by
    intro a ha
    have hle : a ≤ ((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) := by
      have h := Theses.A.VN.le_norm_smul_one ha
      simpa [Complex.coe_smul] using h
    have hb : (0 : effCarrier) ≤ ((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a :=
      sub_nonneg.mpr hle
    have h2 := hdom _ hb
    have hval : ((truth (suI.{u})).unop.toNCPMap
          (((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a)).down
        = ((‖a‖ : ℝ) : ℂ) - ((truth (suI.{u})).unop.toNCPMap a).down := by
      have hlin : (truth (suI.{u})).unop.toNCPMap
            (((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a)
          = ((‖a‖ : ℝ) : ℂ) • (truth (suI.{u})).unop.toNCPMap (1 : effCarrier)
            - (truth (suI.{u})).unop.toNCPMap a := by
        rw [show (truth (suI.{u})).unop.toNCPMap
              (((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a)
            = ncpLin (truth (suI.{u})).unop.toNCPMap
              (((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a) from rfl,
          map_sub, map_smul]
        rfl
      rw [hlin, hφ1]
      show ((‖a‖ : ℝ) : ℂ) * 1 - ((truth (suI.{u})).unop.toNCPMap a).down
        = ((‖a‖ : ℝ) : ℂ) - ((truth (suI.{u})).unop.toNCPMap a).down
      rw [mul_one]
    rw [hval] at h2
    refine le_antisymm ?_ (hdom a ha)
    have h4 := sub_nonneg.mpr h2
    have h5 : (((‖a‖ : ℝ) : ℂ) • (1 : effCarrier) - a)
          - ((((‖a‖ : ℝ) : ℂ) - ((truth (suI.{u})).unop.toNCPMap a).down)
            • (1 : effCarrier))
        = ((truth (suI.{u})).unop.toNCPMap a).down • (1 : effCarrier) - a := by
      rw [sub_smul]; abel
    rw [h5] at h4
    exact sub_nonneg.mp h4
  -- hence every element is
  have hall : ∀ a : effCarrier,
      ((truth (suI.{u})).unop.toNCPMap a).down • (1 : effCarrier) = a := by
    have hlin : ∀ x : effCarrier, 0 ≤ x →
        ((ncpLin (suOne (effObj (WStarCPSU.{u}ᵒᵖ)) ≫ truth (suI.{u})).unop.toNCPMap
          - LinearMap.id : effCarrier →ₗ[ℂ] effCarrier)) x = 0 := by
      intro x hx
      show (suOne (effObj (WStarCPSU.{u}ᵒᵖ)) ≫ truth (suI.{u})).unop.toNCPMap x - x = 0
      rw [hk x, ← hnorm x hx, sub_self]
    intro a
    have h := linear_eq_zero_of_nonneg hlin a
    have h' : (suOne (effObj (WStarCPSU.{u}ᵒᵖ)) ≫ truth (suI.{u})).unop.toNCPMap a - a
        = 0 := h
    rw [hk a] at h'
    exact sub_eq_zero.mp h'
  -- the truth predicate is unital at every object
  have hone : ∀ X : WStarCPSU.{u}ᵒᵖ,
      (truth X).unop.toNCPMap (1 : effCarrier) = 1 := by
    intro X
    have hq := su_pred_le_truth' X (suOne X ≫ truth (suI.{u}))
      (a := (1 : effCarrier)) zero_le_one
    have hq1 : (suOne X ≫ truth (suI.{u})).unop.toNCPMap (1 : effCarrier) = 1 := by
      rw [suop_comp_apply, hφ1]
      show (1 : ULift.{u} ℂ).down • (1 : X.unop.base.carrier) = 1
      simp
    rw [hq1] at hq
    exact le_antisymm (truth X).unop.subunital' hq
  refine ⟨⟨suOne (effObj (WStarCPSU.{u}ᵒᵖ)), truth (suI.{u}), ?_, ?_⟩, ?_⟩
  · refine suop_hom_ext fun a => ?_
    rw [hk a, hall a]
    exact (su_id_apply a).symm
  · refine suop_hom_ext fun z => ?_
    refine Eq.trans ?_ (su_id_apply (X := (suI.{u}).unop) z).symm
    rw [suop_comp_apply]
    show (truth (suI.{u})).unop.toNCPMap (z.down • (1 : effCarrier)) = z
    rw [show (truth (suI.{u})).unop.toNCPMap (z.down • (1 : effCarrier))
      = ncpLin (truth (suI.{u})).unop.toNCPMap (z.down • (1 : effCarrier)) from rfl,
      map_smul]
    show z.down • (truth (suI.{u})).unop.toNCPMap (1 : effCarrier) = z
    rw [hφ1]
    exact Theses.A.VN.CU.down_injective (by show z.down * (1 : ℂ) = z.down; rw [mul_one])
  · intro X
    refine suop_hom_ext fun z => ?_
    rw [suop_comp_apply]
    show (truth X).unop.toNCPMap (z.down • (1 : effCarrier))
      = z.down • (1 : X.unop.base.carrier)
    rw [show (truth X).unop.toNCPMap (z.down • (1 : effCarrier))
      = ncpLin (truth X).unop.toNCPMap (z.down • (1 : effCarrier)) from rfl,
      map_smul]
    show z.down • (truth X).unop.toNCPMap (1 : effCarrier)
      = z.down • (1 : X.unop.base.carrier)
    rw [hone X]

/-- **The total maps of `vN_cpsuᵒᵖ` are the ncpu-maps**, for *any*
partial-form effectus structure on it: `f` is total iff it is unital. -/
theorem su_isTotal_iff {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    IsTotal f ↔ f.unop.toNCPMap 1 = 1 := by
  obtain ⟨θ, hθ⟩ := su_effObj_iso.{u}
  have hhom : θ.hom = suOne (effObj (WStarCPSU.{u}ᵒᵖ)) := by
    have h := hθ (effObj (WStarCPSU.{u}ᵒᵖ))
    rwa [one_m_is_id, Category.id_comp] at h
  have htr : ∀ (Z : WStarCPSU.{u}ᵒᵖ) (a : effCarrier),
      (truth Z).unop.toNCPMap a
        = (θ.inv.unop.toNCPMap a).down • (1 : Z.unop.base.carrier) := by
    intro Z a
    have e : truth Z = suOne Z ≫ θ.inv := by
      rw [← hθ Z, Category.assoc, θ.hom_inv_id, Category.comp_id]
    rw [e, suop_comp_apply]
    rfl
  have hinv1 : θ.inv.unop.toNCPMap (1 : effCarrier) = (1 : ULift.{u} ℂ) := by
    have h : (θ.inv ≫ θ.hom).unop.toNCPMap
          (1 : (Opposite.unop (suI.{u})).base.carrier)
        = (𝟙 (suI.{u}) : suI.{u} ⟶ suI.{u}).unop.toNCPMap
          (1 : (Opposite.unop (suI.{u})).base.carrier) :=
      congrArg (fun k : suI.{u} ⟶ suI.{u} =>
        k.unop.toNCPMap (1 : (Opposite.unop (suI.{u})).base.carrier)) θ.inv_hom_id
    rw [suop_comp_apply, hhom] at h
    refine Eq.trans ?_ (su_id_apply (X := (suI.{u}).unop) 1)
    refine Eq.trans (congrArg θ.inv.unop.toNCPMap ?_) h
    show (1 : effCarrier) = (1 : ULift.{u} ℂ).down • (1 : effCarrier)
    rw [Theses.A.VN.CU.down_one, one_smul]
  have hone : ∀ Z : WStarCPSU.{u}ᵒᵖ,
      (truth Z).unop.toNCPMap (1 : effCarrier) = (1 : Z.unop.base.carrier) := by
    intro Z
    rw [htr Z 1, hinv1, Theses.A.VN.CU.down_one, one_smul]
  constructor
  · intro hf
    have h := congrArg (fun k : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ) =>
      k.unop.toNCPMap (1 : effCarrier)) hf
    rw [suop_comp_apply, hone Y, hone X] at h
    exact h
  · intro hf
    refine suop_hom_ext fun a => ?_
    rw [suop_comp_apply, htr Y a, htr X a,
      show f.unop.toNCPMap ((θ.inv.unop.toNCPMap a).down • (1 : Y.unop.base.carrier))
        = ncpLin f.unop.toNCPMap
          ((θ.inv.unop.toNCPMap a).down • (1 : Y.unop.base.carrier)) from rfl,
      map_smul]
    show (θ.inv.unop.toNCPMap a).down • f.unop.toNCPMap (1 : Y.unop.base.carrier)
      = (θ.inv.unop.toNCPMap a).down • (1 : X.unop.base.carrier)
    rw [hf]

/-! ### `vN_cpsuᵒᵖ` is real, with separating states and predicates (190III)

All three claims are read off the isomorphism `θ : I ≅ ℂᵤ` of
`su_effObj_iso`.  Writing `μ = θ.inv.unop` for the induced isomorphism
`I → ℂᵤ` (so that `a = μ(a)·1` for every `a` of the effect algebra):

* **separating predicates** — an effect `a ∈ [0,1]_X` gives the predicate
  `(z ↦ z·a) ≫ θ.inv`, and composing with it reads off `f(a)`; every
  positive element is a positive multiple of an effect, so `f = g` follows by
  linearity (`linear_eq_zero_of_nonneg`).
* **separating states** — by `su_isTotal_iff` the states of `X` are exactly
  the normal states of the algebra `X.unop`, and those separate its elements
  (`eq_zero_of_ncpsu_states`).
* **real** — `μ` carries `Scal C = C(I,I)` onto `[0,1] ⊆ ℝ` by an
  *isomorphism* of effect monoids, taking `⋁` to `+` and composition to
  multiplication.

**On the reality conjunct** (audit row 190II.3).
`IsRealEffectus` (`StatesPredicates.lean`) asks — as **190II.3**
(`dfn-mandso`, eff.tex:2097) does — for an *isomorphism* of effect monoids
`Scal C ≅ [0,1]`, i.e. a mutually inverse pair of morphisms, and not merely
for a bijective morphism: a bijective morphism of effect algebras need not
be an isomorphism, since the inverse has to **reflect** `⊥`, which no axiom
gives.  Here it does: `k(1) = s(k)·1`, so `k ⊥ l` is *equivalent* to
`s k + s l ≤ 1` (`hperp_refl` in the proof), and the set-theoretic inverse
`s'` of `s` is therefore itself a morphism.  That is what discharges the
first conjunct below. -/
theorem su_real_separating :
    IsRealEffectus (WStarCPSU.{u}ᵒᵖ) ∧
      SeparatingPredicates (WStarCPSU.{u}ᵒᵖ) ∧
      SeparatingStates (WStarCPSU.{u}ᵒᵖ) := by
  obtain ⟨θ, hθ⟩ := su_effObj_iso.{u}
  have hhom : θ.hom = suOne (effObj (WStarCPSU.{u}ᵒᵖ)) := by
    have h := hθ (effObj (WStarCPSU.{u}ᵒᵖ))
    rwa [one_m_is_id, Category.id_comp] at h
  have hhomap : ∀ z : ULift.{u} ℂ,
      θ.hom.unop.toNCPMap z = z.down • (1 : effCarrier) := by
    intro z
    rw [hhom]
    rfl
  have hinvhom : ∀ z : ULift.{u} ℂ,
      θ.inv.unop.toNCPMap (θ.hom.unop.toNCPMap z) = z := by
    intro z
    exact (suop_comp_apply θ.inv θ.hom z).symm.trans
      ((suop_congr θ.inv_hom_id z).trans (su_id_apply (X := (suI.{u}).unop) z))
  have hall : ∀ a : effCarrier,
      (θ.inv.unop.toNCPMap a).down • (1 : effCarrier) = a := by
    intro a
    refine (hhomap (θ.inv.unop.toNCPMap a)).symm.trans ?_
    exact (suop_comp_apply θ.hom θ.inv a).symm.trans
      ((suop_congr θ.hom_inv_id a).trans (su_id_apply a))
  have hinv1 : θ.inv.unop.toNCPMap (1 : effCarrier) = (1 : ULift.{u} ℂ) := by
    have h := hinvhom 1
    rwa [hhomap, Theses.A.VN.CU.down_one, one_smul] at h
  -- ### separating predicates
  have hsepP : SeparatingPredicates (WStarCPSU.{u}ᵒᵖ) := by
    intro Y X f g hfg
    -- the predicates of `X` include the concrete effects of `X.unop`
    have key : ∀ (a : X.unop.base.carrier) (h0 : 0 ≤ a) (h1 : a ≤ 1),
        f.unop.toNCPMap a = g.unop.toNCPMap a := by
      intro a h0 h1
      have hq : ∀ k : Y ⟶ X,
          (k ≫ (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv)).unop.toNCPMap
            (1 : effCarrier) = k.unop.toNCPMap a := by
        intro k
        rw [suop_comp_apply, suop_comp_apply, hinv1]
        show k.unop.toNCPMap ((1 : ULift.{u} ℂ).down • a) = k.unop.toNCPMap a
        rw [Theses.A.VN.CU.down_one, one_smul]
      have hp := suop_congr (hfg (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv))
        (1 : effCarrier)
      rw [hq f, hq g] at hp
      exact hp
    -- every positive element is a positive multiple of an effect
    have hpos : ∀ b : X.unop.base.carrier, 0 ≤ b →
        f.unop.toNCPMap b = g.unop.toNCPMap b := by
      intro b hb
      have hnorm : (0 : ℝ) < ‖b‖ + 1 := by positivity
      have hr0 : (0 : ℝ) ≤ (‖b‖ + 1)⁻¹ := le_of_lt (inv_pos.mpr hnorm)
      have hle : b ≤ ((‖b‖ : ℝ) : ℂ) • (1 : X.unop.base.carrier) := by
        have h := Theses.A.VN.le_norm_smul_one hb
        simpa [Complex.coe_smul] using h
      have h0 : (0 : X.unop.base.carrier) ≤ (((‖b‖ + 1)⁻¹ : ℝ) : ℂ) • b :=
        cstar_positive_1 b hb _ hr0
      have h1 : (((‖b‖ + 1)⁻¹ : ℝ) : ℂ) • b ≤ 1 := by
        refine le_trans (smul_le_smul_cstar hr0 hle) ?_
        rw [smul_smul, show ((((‖b‖ + 1)⁻¹ : ℝ) : ℂ) * ((‖b‖ : ℝ) : ℂ))
            = ((((‖b‖ + 1)⁻¹ * ‖b‖ : ℝ)) : ℂ) by push_cast; ring]
        refine smul_one_le_one (by positivity) ?_
        rw [inv_mul_eq_div]
        exact (div_le_one hnorm).mpr (by linarith)
      have hkey := key _ h0 h1
      rw [ncp_smul_apply f.unop.toNCPMap, ncp_smul_apply g.unop.toNCPMap] at hkey
      have h2 := congrArg (fun z : Y.unop.base.carrier =>
        (((‖b‖ + 1 : ℝ)) : ℂ) • z) hkey
      simp only [smul_smul] at h2
      rwa [show ((((‖b‖ + 1 : ℝ)) : ℂ) * ((((‖b‖ + 1)⁻¹ : ℝ)) : ℂ)) = 1 by
        push_cast; field_simp, one_smul, one_smul] at h2
    refine suop_hom_ext fun a => ?_
    have hlin : ∀ x : X.unop.base.carrier, 0 ≤ x →
        ((ncpLin f.unop.toNCPMap - ncpLin g.unop.toNCPMap :
          X.unop.base.carrier →ₗ[ℂ] Y.unop.base.carrier)) x = 0 := by
      intro x hx
      show f.unop.toNCPMap x - g.unop.toNCPMap x = 0
      rw [hpos x hx, sub_self]
    have h := linear_eq_zero_of_nonneg hlin a
    have h' : f.unop.toNCPMap a - g.unop.toNCPMap a = 0 := h
    exact sub_eq_zero.mp h'
  -- ### separating states
  have hsepS : SeparatingStates (WStarCPSU.{u}ᵒᵖ) := by
    intro X Y f g hfg
    have hpos : ∀ c : Y.unop.base.carrier, 0 ≤ c →
        f.unop.toNCPMap c = g.unop.toNCPMap c := by
      intro c hc
      have hfc : (0 : X.unop.base.carrier) ≤ f.unop.toNCPMap c :=
        ncpsu_nonneg _ hc
      have hgc : (0 : X.unop.base.carrier) ≤ g.unop.toNCPMap c :=
        ncpsu_nonneg _ hc
      have hsa : IsSelfAdjoint (f.unop.toNCPMap c - g.unop.toNCPMap c) :=
        hfc.isSelfAdjoint.sub hgc.isSelfAdjoint
      refine sub_eq_zero.mp (eq_zero_of_ncpsu_states X.unop.base.carrier hsa ?_)
      intro ψ hψ1
      -- `θ.hom ≫ ψ` is a state of `X`
      have htot : IsTotal (θ.hom ≫ Quiver.Hom.op ψ) := by
        rw [su_isTotal_iff, suop_comp_apply]
        show θ.hom.unop.toNCPMap (ψ.toNCPMap (1 : X.unop.base.carrier)) = 1
        rw [hψ1, hhomap, Theses.A.VN.CU.down_one, one_smul]
      have h := suop_congr (hfg ⟨θ.hom ≫ Quiver.Hom.op ψ, htot⟩) c
      rw [suop_comp_apply, suop_comp_apply, suop_comp_apply,
        suop_comp_apply] at h
      have h2 : ψ.toNCPMap (f.unop.toNCPMap c) = ψ.toNCPMap (g.unop.toNCPMap c) := by
        have h3 := congrArg (fun z : effCarrier => θ.inv.unop.toNCPMap z) h
        exact ((hinvhom (ψ.toNCPMap (f.unop.toNCPMap c))).symm.trans h3).trans
          (hinvhom (ψ.toNCPMap (g.unop.toNCPMap c)))
      show ψ.toNCPMap (f.unop.toNCPMap c - g.unop.toNCPMap c) = 0
      rw [show ψ.toNCPMap (f.unop.toNCPMap c - g.unop.toNCPMap c)
          = ncpLin ψ.toNCPMap (f.unop.toNCPMap c - g.unop.toNCPMap c) from rfl,
        map_sub]
      show ψ.toNCPMap (f.unop.toNCPMap c) - ψ.toNCPMap (g.unop.toNCPMap c) = 0
      rw [h2, sub_self]
    refine suop_hom_ext fun b => ?_
    have hlin : ∀ x : Y.unop.base.carrier, 0 ≤ x →
        ((ncpLin f.unop.toNCPMap - ncpLin g.unop.toNCPMap :
          Y.unop.base.carrier →ₗ[ℂ] X.unop.base.carrier)) x = 0 := by
      intro x hx
      show f.unop.toNCPMap x - g.unop.toNCPMap x = 0
      rw [hpos x hx, sub_self]
    have h := linear_eq_zero_of_nonneg hlin b
    have h' : f.unop.toNCPMap b - g.unop.toNCPMap b = 0 := h
    exact sub_eq_zero.mp h'
  -- ### the scalars are `[0,1]`
  obtain ⟨t, ht⟩ : ∃ t : Scal (WStarCPSU.{u}ᵒᵖ) → ℂ,
      ∀ k : Scal (WStarCPSU.{u}ᵒᵖ),
        t k = (θ.inv.unop.toNCPMap (k.unop.toNCPMap (1 : effCarrier))).down :=
    ⟨_, fun _ => rfl⟩
  have ht0 : ∀ k, (0 : ℂ) ≤ t k := by
    intro k
    rw [ht]
    exact ncpsu_nonneg θ.inv.unop (ncpsu_nonneg k.unop zero_le_one)
  have ht1 : ∀ k, t k ≤ 1 := by
    intro k
    rw [ht]
    have h := ncpsu_mono θ.inv.unop k.unop.subunital'
    rw [hinv1] at h
    exact h
  have htre : ∀ k, (((t k).re : ℝ) : ℂ) = t k := by
    intro k
    obtain ⟨-, him⟩ := Complex.le_def.mp (ht0 k)
    refine Complex.ext (by simp) ?_
    simpa using him
  obtain ⟨s, hs⟩ : ∃ s : Scal (WStarCPSU.{u}ᵒᵖ) → unitInterval,
      ∀ k, ((s k : ℝ) : ℂ) = t k := by
    refine ⟨fun k => ⟨(t k).re, ?_, ?_⟩, fun k => htre k⟩
    · simpa using (Complex.le_def.mp (ht0 k)).1
    · simpa using (Complex.le_def.mp (ht1 k)).1
  -- `k` is determined by `k(1)`, which is the scalar `t k`
  have hunop : ∀ (k : Scal (WStarCPSU.{u}ᵒᵖ)) (a : effCarrier),
      k.unop.toNCPMap a
        = (θ.inv.unop.toNCPMap a).down • k.unop.toNCPMap (1 : effCarrier) := by
    intro k a
    conv_lhs => rw [← hall a]
    exact ncp_smul_apply k.unop.toNCPMap _ 1
  have hone : t 1 = 1 := by
    have h1 : (1 : Scal (WStarCPSU.{u}ᵒᵖ)).unop.toNCPMap (1 : effCarrier)
        = (1 : effCarrier) := by
      rw [show (1 : Scal (WStarCPSU.{u}ᵒᵖ)) = 𝟙 (effObj (WStarCPSU.{u}ᵒᵖ)) from
        one_m_is_id]
      exact su_id_apply (1 : effCarrier)
    rw [ht, h1, hinv1]
    simp
  have hmul : ∀ k l : Scal (WStarCPSU.{u}ᵒᵖ), t (k * l) = t k * t l := by
    intro k l
    simp only [ht]
    show (θ.inv.unop.toNCPMap ((l ≫ k).unop.toNCPMap (1 : effCarrier))).down
      = (θ.inv.unop.toNCPMap (k.unop.toNCPMap 1)).down
        * (θ.inv.unop.toNCPMap (l.unop.toNCPMap 1)).down
    rw [suop_comp_apply, hunop l (k.unop.toNCPMap 1),
      ncp_smul_apply θ.inv.unop.toNCPMap]
    rfl
  have hadd : ∀ (k l : Scal (WStarCPSU.{u}ᵒᵖ)) (h : Perp k l),
      t (ovee k l h) = t k + t l := by
    intro k l h
    simp only [ht]
    rw [show (ovee k l h).unop.toNCPMap (1 : effCarrier)
        = k.unop.toNCPMap 1 + l.unop.toNCPMap 1 from rfl, ncp_add_apply]
    rfl
  have hperp : ∀ (k l : Scal (WStarCPSU.{u}ᵒᵖ)), Perp k l → t k + t l ≤ 1 := by
    intro k l h
    have h' : k.unop.toNCPMap (1 : effCarrier) + l.unop.toNCPMap 1 ≤ 1 := h
    have h2 := ncpsu_mono θ.inv.unop h'
    rw [hinv1, ncp_add_apply] at h2
    simp only [ht]
    exact h2
  -- `s` is a morphism of effect monoids
  have hsperp : ∀ {k l : Scal (WStarCPSU.{u}ᵒᵖ)}, Perp k l → Perp (s k) (s l) := by
    intro k l h
    show ((s k : ℝ)) + ((s l : ℝ)) ≤ 1
    have h2 := hperp k l h
    rw [← hs, ← hs] at h2
    obtain ⟨h3, -⟩ := Complex.le_def.mp h2
    simpa using h3
  have hsovee : ∀ {k l : Scal (WStarCPSU.{u}ᵒᵖ)} (h : Perp k l),
      s (ovee k l h) = ovee (s k) (s l) (hsperp h) := by
    intro k l h
    refine Subtype.ext ?_
    show ((s (ovee k l h) : ℝ)) = ((s k : ℝ)) + ((s l : ℝ))
    have h2 := hadd k l h
    rw [← hs, ← hs, ← hs] at h2
    exact_mod_cast h2
  have hsone : s 1 = 1 := by
    refine Subtype.ext ?_
    show ((s 1 : ℝ)) = 1
    have h2 := hone
    rw [← hs] at h2
    exact_mod_cast h2
  have hsmul : ∀ k l : Scal (WStarCPSU.{u}ᵒᵖ), s (k * l) = s k * s l := by
    intro k l
    refine Subtype.ext ?_
    show ((s (k * l) : ℝ)) = ((s k : ℝ)) * ((s l : ℝ))
    have h2 := hmul k l
    rw [← hs, ← hs, ← hs] at h2
    exact_mod_cast h2
  have hsinj : Function.Injective s := by
    intro k l hkl
    have hkl' : s k = s l := hkl
    have h2 : t k = t l := by rw [← hs, ← hs, hkl']
    have h1 : k.unop.toNCPMap (1 : effCarrier) = l.unop.toNCPMap 1 := by
      rw [← hall (k.unop.toNCPMap 1), ← hall (l.unop.toNCPMap 1), ← ht k, ← ht l,
        h2]
    exact suop_hom_ext fun a => by rw [hunop k a, hunop l a, h1]
  have hssurj : Function.Surjective s := by
    intro r
    have h0 : (0 : ULift.{u} ℂ) ≤ ((r : ℝ) : ℂ) • (1 : ULift.{u} ℂ) :=
      cstar_positive_1 1 zero_le_one _ r.2.1
    have h1 : ((r : ℝ) : ℂ) • (1 : ULift.{u} ℂ) ≤ 1 :=
      smul_one_le_one r.2.1 r.2.2
    refine ⟨θ.hom ≫ (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv), ?_⟩
    refine Subtype.ext ?_
    have h2 : t (θ.hom ≫ (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv))
        = ((r : ℝ) : ℂ) := by
      rw [ht, suop_comp_apply, suop_comp_apply, hinv1]
      show (θ.inv.unop.toNCPMap (θ.hom.unop.toNCPMap
        ((1 : ULift.{u} ℂ).down • (((r : ℝ) : ℂ) • (1 : ULift.{u} ℂ))))).down
        = ((r : ℝ) : ℂ)
      rw [Theses.A.VN.CU.down_one, one_smul, hinvhom]
      show ((r : ℝ) : ℂ) * 1 = ((r : ℝ) : ℂ)
      rw [mul_one]
    have h3 := hs (θ.hom ≫ (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv))
    rw [h2] at h3
    show ((s (θ.hom ≫ (Quiver.Hom.op (wEffect h0 h1) ≫ θ.inv)) : ℝ)) = (r : ℝ)
    exact_mod_cast h3
  -- **`s` reflects `⊥`**, and this is what makes the inverse a morphism:
  -- `k(1) = s(k)·1` and `l(1) = s(l)·1`, so `k(1) + l(1) = (s k + s l)·1 ≤ 1`
  -- as soon as `s k + s l ≤ 1` in `[0,1]`.
  have hperp_refl : ∀ k l : Scal (WStarCPSU.{u}ᵒᵖ),
      ((s k : ℝ) + (s l : ℝ) ≤ 1) → Perp k l := by
    intro k l h
    have hk : k.unop.toNCPMap (1 : effCarrier)
        = (((s k : ℝ) : ℂ)) • (1 : effCarrier) := by
      rw [hs k, ht k]
      exact (hall _).symm
    have hl : l.unop.toNCPMap (1 : effCarrier)
        = (((s l : ℝ) : ℂ)) • (1 : effCarrier) := by
      rw [hs l, ht l]
      exact (hall _).symm
    show k.unop.toNCPMap (1 : effCarrier) + l.unop.toNCPMap 1 ≤ 1
    rw [hk, hl, ← add_smul, ← Complex.ofReal_add]
    exact smul_one_le_one (add_nonneg (s k).2.1 (s l).2.1) h
  -- the inverse of `s`, and the four clauses that make it a morphism
  haveI : Nonempty (Scal (WStarCPSU.{u}ᵒᵖ)) := ⟨𝟙 _⟩
  obtain ⟨s', hs'left, hs'right⟩ :
      ∃ s' : unitInterval → Scal (WStarCPSU.{u}ᵒᵖ),
        (∀ k, s' (s k) = k) ∧ ∀ r, s (s' r) = r :=
    ⟨Function.invFun s, Function.leftInverse_invFun hsinj,
      Function.rightInverse_invFun hssurj⟩
  have hs'perp : ∀ {r r' : unitInterval}, Perp r r' → Perp (s' r) (s' r') := by
    intro r r' h
    refine hperp_refl _ _ ?_
    rw [hs'right r, hs'right r']
    exact h
  have hs'ovee : ∀ {r r' : unitInterval} (h : Perp r r'),
      s' (ovee r r' h) = ovee (s' r) (s' r') (hs'perp h) := by
    intro r r' h
    refine hsinj ?_
    rw [hs'right, hsovee]
    refine Subtype.ext ?_
    show ((r : ℝ) + (r' : ℝ)) = ((s (s' r) : ℝ)) + ((s (s' r') : ℝ))
    rw [hs'right, hs'right]
  have hs'one : s' 1 = 1 := hsinj (by rw [hs'right, hsone])
  have hs'mul : ∀ r r' : unitInterval, s' (r * r') = s' r * s' r' :=
    fun r r' => hsinj (by rw [hs'right, hsmul, hs'right, hs'right])
  refine ⟨⟨{ toEAHom := { toPCMHom := { toFun := s
                                        perp_map := hsperp
                                        ovee_map := hsovee }
                          map_one := hsone }
             map_mul := hsmul },
     { toEAHom := { toPCMHom := { toFun := s'
                                  perp_map := hs'perp
                                  ovee_map := hs'ovee }
                    map_one := hs'one }
       map_mul := hs'mul }, hs'left, hs'right⟩, hsepP, hsepS⟩

/-! ### The bridge layer: predicates are effects (parsecs 197–203)

Everything below 190III in this file — the ⋄-effectus of 206III, the sharp
maps of 210III, the dilations of 221III — needs the *concrete*
identification of the effectus notions in `vN_cpsuᵒᵖ`, and eff.tex gives
these as bare `Examples` with no proof:

| eff.tex | notion | in `vNᵒᵖ` |
|---|---|---|
| 3684 | quotients | **filters** (dils.tex 169VIII) |
| 3934 | comprehensions | **corners** (dils.tex 169II) |
| 4195 | sharp predicates | projections |
| 4040 | pure maps | filters after corners |
| 4777 | sharp maps | nmiu-maps |

⚠️ Note the pairing: **quotients are filters and comprehensions are
corners**, not the other way round (eff.tex:3686 and eff.tex:3935; the
Remarks at dils.tex:6072 and dils.tex:6140 say the same, each calling the
effectus-side notion "the direction-reversed counterpart").

The first step is the dictionary itself.  A predicate `p : X ⟶ I` is an
ncpsu-map `I.unop → X.unop`, and `I.unop ≅ ℂ` by `su_effObj_iso`, so `p` is
determined by, and may be chosen freely as, the effect `p(1)` of `X.unop`.
`suPredVal` is that effect, and `su_pred_ext`/`su_pred_exists` are the two
halves of the bijection.  Composition, truth and orthocomplement are then
computed by `su_predVal_comp`, `su_predVal_truth` and `su_predVal_orth`, and
the algebraic order `≼` of the effect algebra is the C\*-order
(`su_pred_le_iff`). -/

/-- The data of `su_effObj_iso` in the form the bridge uses: an ncpsu-map
`μ : I.unop → ℂᵤ` with `μ(1) = 1`, `μ(a)·1 = a`, and `1_X(1) = 1` for every
`X`.  (This is exactly what the proofs of `su_isTotal_iff` and
`su_real_separating` extract from `θ` before they start.) -/
private theorem su_effObj_data :
    ∃ μ : Theses.NCPSUMap (effCarrier.{u}) ((Opposite.unop (suI.{u})).base.carrier),
      (∀ a : effCarrier, (μ.toNCPMap a).down • (1 : effCarrier) = a) ∧
        (∀ X : WStarCPSU.{u}ᵒᵖ,
          (truth X).unop.toNCPMap (1 : effCarrier) = (1 : X.unop.base.carrier)) ∧
        ∀ (X : WStarCPSU.{u}ᵒᵖ) (a : X.unop.base.carrier), 0 ≤ a → a ≤ 1 →
          ∃ p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
            p.unop.toNCPMap (1 : effCarrier) = a := by
  obtain ⟨θ, hθ⟩ := su_effObj_iso.{u}
  have hhom : θ.hom = suOne (effObj (WStarCPSU.{u}ᵒᵖ)) := by
    have h := hθ (effObj (WStarCPSU.{u}ᵒᵖ))
    rwa [one_m_is_id, Category.id_comp] at h
  have hhomap : ∀ z : ULift.{u} ℂ,
      θ.hom.unop.toNCPMap z = z.down • (1 : effCarrier) := by
    intro z
    rw [hhom]
    rfl
  -- `μ(1) = 1`
  have hinv1 : θ.inv.unop.toNCPMap (1 : effCarrier) = (1 : ULift.{u} ℂ) := by
    have h : (θ.inv ≫ θ.hom).unop.toNCPMap
          (1 : (Opposite.unop (suI.{u})).base.carrier)
        = (𝟙 (suI.{u}) : suI.{u} ⟶ suI.{u}).unop.toNCPMap
          (1 : (Opposite.unop (suI.{u})).base.carrier) :=
      congrArg (fun k : suI.{u} ⟶ suI.{u} =>
        k.unop.toNCPMap (1 : (Opposite.unop (suI.{u})).base.carrier)) θ.inv_hom_id
    rw [suop_comp_apply, hhom] at h
    refine Eq.trans ?_ (su_id_apply (X := (suI.{u}).unop) 1)
    refine Eq.trans (congrArg θ.inv.unop.toNCPMap ?_) h
    show (1 : effCarrier) = (1 : ULift.{u} ℂ).down • (1 : effCarrier)
    rw [Theses.A.VN.CU.down_one, one_smul]
  -- `μ(a)·1 = a`, from `θ.hom ≫ θ.inv = 𝟙`
  have hscal : ∀ a : effCarrier, (θ.inv.unop.toNCPMap a).down • (1 : effCarrier) = a := by
    intro a
    have h : (θ.hom ≫ θ.inv).unop.toNCPMap a
        = (𝟙 (effObj (WStarCPSU.{u}ᵒᵖ))).unop.toNCPMap a :=
      congrArg (fun k : effObj (WStarCPSU.{u}ᵒᵖ) ⟶ effObj (WStarCPSU.{u}ᵒᵖ) =>
        k.unop.toNCPMap a) θ.hom_inv_id
    rw [suop_comp_apply] at h
    -- `rw [hhomap]` cannot cross `(Opposite.unop suI).base.carrier` vs `ULift ℂ`
    exact Eq.trans (hhomap (θ.inv.unop.toNCPMap a)).symm
      (h.trans (su_id_apply (X := (effObj (WStarCPSU.{u}ᵒᵖ)).unop) a))
  -- `1_X(1) = 1`
  have hone : ∀ X : WStarCPSU.{u}ᵒᵖ,
      (truth X).unop.toNCPMap (1 : effCarrier) = (1 : X.unop.base.carrier) := by
    intro X
    have e : truth X = suOne X ≫ θ.inv := by
      rw [← hθ X, Category.assoc, θ.hom_inv_id, Category.comp_id]
    have h : (truth X).unop.toNCPMap (1 : effCarrier)
        = (θ.inv.unop.toNCPMap (1 : effCarrier)).down • (1 : X.unop.base.carrier) := by
      rw [e, suop_comp_apply]
      rfl
    rw [h, hinv1, Theses.A.VN.CU.down_one, one_smul]
  -- every effect is named by a predicate
  have hex : ∀ (X : WStarCPSU.{u}ᵒᵖ) (a : X.unop.base.carrier), 0 ≤ a → a ≤ 1 →
      ∃ p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
        p.unop.toNCPMap (1 : effCarrier) = a := by
    intro X a h0 h1
    -- the ascription `X ⟶ suI` is essential: without it `Quiver.Hom.op` has to
    -- solve `?P.base.carrier =?= ULift ℂ`, which diverges (`WStar.of` is
    -- semireducible)
    obtain ⟨q, hq⟩ : ∃ q : X ⟶ suI.{u},
        ∀ z : (Opposite.unop (suI.{u})).base.carrier,
          q.unop.toNCPMap z = z.down • a :=
      ⟨Quiver.Hom.op (wEffect h0 h1), fun _ => rfl⟩
    refine ⟨q ≫ θ.inv, ?_⟩
    refine Eq.trans (suop_comp_apply q θ.inv (1 : effCarrier)) ?_
    rw [hq, hinv1, Theses.A.VN.CU.down_one, one_smul]
  exact ⟨θ.inv.unop, hscal, hone, hex⟩

/-- **The predicate–effect dictionary.**  The effect of `X.unop` named by a
predicate `p` on `X`, namely `p(1)`. -/
noncomputable def suPredVal {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) : X.unop.base.carrier :=
  p.unop.toNCPMap (1 : effCarrier)

theorem suPredVal_def {X : WStarCPSU.{u}ᵒᵖ} (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    suPredVal p = p.unop.toNCPMap (1 : effCarrier) := rfl

theorem suPredVal_nonneg {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) : 0 ≤ suPredVal p :=
  ncpsu_one_nonneg _

theorem suPredVal_le_one {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) : suPredVal p ≤ 1 :=
  p.unop.subunital'

/-- Composition: `suPredVal (f ≫ p) = f(suPredVal p)`. -/
theorem suPredVal_comp {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (p : Y ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    suPredVal (f ≫ p) = f.unop.toNCPMap (suPredVal p) :=
  suop_comp_apply f p (1 : effCarrier)

/-- The truth predicate names `1`. -/
theorem suPredVal_truth (X : WStarCPSU.{u}ᵒᵖ) :
    suPredVal (truth X) = (1 : X.unop.base.carrier) := by
  obtain ⟨μ, -, hone, -⟩ := su_effObj_data.{u}
  exact hone X

/-- A predicate is determined by the effect it names. -/
theorem su_pred_ext {X : WStarCPSU.{u}ᵒᵖ}
    {p q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} (h : suPredVal p = suPredVal q) :
    p = q := by
  obtain ⟨μ, hscal, -, -⟩ := su_effObj_data.{u}
  have key : ∀ (k : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (a : effCarrier),
      k.unop.toNCPMap a = (μ.toNCPMap a).down • suPredVal k := by
    intro k a
    exact Eq.trans (congrArg k.unop.toNCPMap (hscal a).symm)
      (map_smul (ncpLin k.unop.toNCPMap) _ _)
  exact suop_hom_ext fun a => by rw [key p a, key q a, h]

/-- Every effect of `X.unop` is named by a predicate on `X`. -/
theorem su_pred_exists {X : WStarCPSU.{u}ᵒᵖ} {a : X.unop.base.carrier}
    (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ∃ p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ), suPredVal p = a := by
  obtain ⟨μ, -, -, hex⟩ := su_effObj_data.{u}
  exact hex X a h0 h1

/-- The orthocomplement of predicates is `a ↦ 1 − a`. -/
theorem suPredVal_orth {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    suPredVal (EffectusPartialForm.orth p) = 1 - suPredVal p := by
  have h : suPredVal p + suPredVal (EffectusPartialForm.orth p)
      = suPredVal (truth X) := su_pred_ovee X p 1
  rw [suPredVal_truth X] at h
  exact eq_sub_of_add_eq' h

/-- The algebraic order of the effect algebra of predicates is the C\*-order
of the effects. -/
theorem su_pred_le_iff {X : WStarCPSU.{u}ᵒᵖ}
    (p q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    p ≼ q ↔ suPredVal p ≤ suPredVal q := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hval : suPredVal (ovee p r hr) = suPredVal p + suPredVal r := rfl
    rw [hval]
    exact le_add_of_nonneg_right (suPredVal_nonneg r)
  · intro hle
    obtain ⟨r, hr⟩ : ∃ r : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
        suPredVal r = suPredVal q - suPredVal p :=
      su_pred_exists (sub_nonneg.mpr hle)
        (le_trans (sub_le_self _ (suPredVal_nonneg p)) (suPredVal_le_one q))
    have hperp : Perp p r := by
      show suPredVal p + suPredVal r ≤ 1
      rw [hr, add_sub_cancel]
      exact suPredVal_le_one q
    refine ⟨r, hperp, su_pred_ext ?_⟩
    show suPredVal p + suPredVal r = suPredVal q
    rw [hr, add_sub_cancel]

/-! ### Images are carriers (eff.tex:4080 at `vNᵒᵖ`)

The image of `f : X ⟶ Y` is the least predicate `q` on `Y` with
`f(q) = f(1)`, i.e. the least effect `q` of `Y.unop` with `f(1 − q) = 0`.
That is **not quite** the carrier `⌈f⌉` of vn.tex 63I, which is the least
such *projection*; but the two agree, because `f(b) = 0` for an effect `b`
forces `f(⌈b⌉) = 0` (`ncp_ceil`, **60V**), and `b ≤ ⌈b⌉`.  So the image
exists and is a projection — which is the first half of "sharp predicates
are projections". -/

/-- The **carrier** `⌈f⌉` of a morphism of `vN_cpsuᵒᵖ`: the least projection
`z` of `Y.unop` with `f(1 − z) = 0` (vn.tex 63I, `Theses.A.VN.carrier`). -/
private noncomputable def suCarrier {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    Y.unop.base.carrier :=
  Theses.A.VN.carrier (Theses.A.VN.ncpPositive f.unop.toNCPMap)
    f.unop.toNCPMap.preservesDirSups'

private theorem su_carrier_spec {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    IsStarProjection (suCarrier f) ∧
      f.unop.toNCPMap (1 - suCarrier f) = 0 ∧
      ∀ q : Y.unop.base.carrier, IsStarProjection q →
        f.unop.toNCPMap (1 - q) = 0 → suCarrier f ≤ q :=
  Theses.A.VN.carrier_spec (Theses.A.VN.ncpPositive f.unop.toNCPMap)
    f.unop.toNCPMap.preservesDirSups'

/-- `f(b) = f(1)` for an effect `b` forces `⌈f⌉ ≤ b`: the carrier is least
not only among projections but among *effects*, by `ncp_ceil`. -/
private theorem su_carrier_le {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    {b : Y.unop.base.carrier} (h0 : 0 ≤ b) (h1 : b ≤ 1)
    (heq : f.unop.toNCPMap b = f.unop.toNCPMap 1) : suCarrier f ≤ b := by
  obtain ⟨-, -, hleast⟩ := su_carrier_spec f
  have hb0 : (0 : Y.unop.base.carrier) ≤ 1 - b := sub_nonneg.mpr h1
  -- `f(1 − b) = 0`
  have hzero : f.unop.toNCPMap (1 - b) = 0 := by
    have hlin : f.unop.toNCPMap (1 - b)
        = f.unop.toNCPMap 1 - f.unop.toNCPMap b :=
      map_sub (ncpLin f.unop.toNCPMap) 1 b
    rw [hlin, heq, sub_self]
  -- hence `f(⌈1 − b⌉) = 0`
  have hceil : f.unop.toNCPMap (Theses.A.VN.ceil (1 - b)) = 0 := by
    have hnc := Theses.A.VN.ncp_ceil (Theses.A.VN.ncpPositive f.unop.toNCPMap)
      f.unop.toNCPMap.preservesDirSups' (1 - b) hb0
    have hl : Theses.A.VN.ceil (f.unop.toNCPMap (1 - b)) = 0 := by
      rw [hzero]; exact Theses.A.VN.ceil_zero
    have hnn : (0 : X.unop.base.carrier)
        ≤ f.unop.toNCPMap (Theses.A.VN.ceil (1 - b)) :=
      ncpsu_nonneg f.unop (Theses.A.VN.ceil_spec hb0).1.nonneg
    exact (Theses.A.VN.ceil_basic_3 _ hnn).mpr (hl ▸ hnc).symm
  -- so `⌈f⌉ ≤ 1 − ⌈1 − b⌉ ≤ b`
  have hle := hleast (1 - Theses.A.VN.ceil (1 - b))
    (Theses.A.VN.ceil_spec hb0).1.one_sub
    (by rw [sub_sub_cancel]; exact hceil)
  refine le_trans hle ?_
  have hbc : (1 : Y.unop.base.carrier) - b ≤ Theses.A.VN.ceil (1 - b) := by
    refine (Theses.A.VN.le_proj_iff ⟨hb0, by simpa using h0⟩
      (Theses.A.VN.ceil_spec hb0).1).mpr ?_
    rw [mul_sub, mul_one, (Theses.A.VN.ceil_spec hb0).2.1, sub_self]
  have := sub_le_sub_left hbc (1 : Y.unop.base.carrier)
  simpa using this

/-! ### Comprehensions are corners, quotients are filters (eff.tex:3934, 3684)

With the dictionary in hand the two universal properties are *literally* the
ones of `Theses/B/Dils/Pure.lean`, read in the opposite category:

* a **comprehension** for `p` on `X` is a map `π : W ⟶ X`, i.e. an ncpsu-map
  `h : X.unop → W.unop`, with `h(a) = h(1)` for `a = suPredVal p`, universal
  among ncpsu-maps out of `X.unop` with that property — that is exactly
  `IsCornerFor h a` (dils.tex 169II), except that `IsCornerFor` quantifies
  over all *ncp*-maps `f`.  That is harmless in both directions: the standard
  corner `h_a : A → ⌊a⌋A⌊a⌋` is **unital** (its unit is `⌊a⌋ = h_a(1)`), so
  the mediating map `f'` of a subunital `f` is again subunital, and
  uniqueness among ncp-maps is stronger than uniqueness among ncpsu-maps.
* a **quotient** for `p` on `X` is a map `ξ : X ⟶ Q`, i.e. an ncpsu-map
  `c : Q.unop → X.unop`, with `c(1) ≼ pᗮ`, universal among ncpsu-maps into
  `X.unop` bounded by `pᗮ` — that is exactly `IsFilterFor c (1 − a)`
  (dils.tex 169VIII, in the form the author ruled on 2026-08-16: the
  mediating map is *subunital*, precisely what a morphism of this category
  is.  The ruling is implemented in `IsFilterFor` (`B/Dils/Pure.lean`), and
  the erratum it settles is the **169VIII** row of `ERRATA.md`).

Both are `Prop`-valued classes with existential fields, so no canonical
choice of corner or filter has to be made. -/

/-- The standard corner `h_a : 𝒜 → ⌊a⌋𝒜⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋` (dils.tex 169IV
`standard_corner_dils`), as a comprehension, together with the three further
facts the rest of the file needs of it: its carrier is `⌊a⌋`, its ncpsu-map
is surjective, and — for the commutative subcategory `CvNᵒᵖ` of 206III — the
corner `⌊a⌋𝒜⌊a⌋` is commutative whenever `𝒜` is, because its multiplication
is that of `𝒜`.  `su_hasComprehension` below is the bare 199V. -/
private theorem su_exists_corner {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃ (W : WStarCPSU.{u}ᵒᵖ) (π : W ⟶ X), IsComprehension p π ∧
      suCarrier π = Theses.A.VN.floor (suPredVal p) ∧
      Function.Surjective π.unop.toNCPMap ∧
      ((∀ x y : X.unop.base.carrier, x * y = y * x) →
        ∀ x y : W.unop.base.carrier, x * y = y * x) := by
    obtain ⟨h, hval, -, hcorner, huniv⟩ := Theses.B.Dils.standard_corner_dils
      (A := X.unop.base.carrier) (suPredVal p)
      ⟨suPredVal_nonneg p, suPredVal_le_one p⟩
    letI : Theses.VonNeumannAlgebra
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.floor (suPredVal p))) :=
      Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
    -- the standard corner is **unital** into `⌊a⌋𝒜⌊a⌋`, whose unit is `⌊a⌋`
    have hunital : h (1 : X.unop.base.carrier) = 1 := by
      refine Theses.B.Dils.cornerSet.val_injective ?_
      rw [hval, Theses.B.Dils.cornerSet.val_one, mul_one]
      exact (Theses.B.Dils.cornerSet.proj
        (Theses.A.VN.floor (suPredVal p))).isIdempotentElem.eq
    obtain ⟨π, hπ⟩ : ∃ π : Opposite.op (WStarCPSU.of (WStar.of
          (Theses.B.Dils.cornerSet X.unop.base.carrier
            (Theses.A.VN.floor (suPredVal p))))) ⟶ X,
        ∀ x : X.unop.base.carrier, π.unop.toNCPMap x = h x :=
      ⟨Quiver.Hom.op ⟨h, le_of_eq hunital⟩, fun _ => rfl⟩
    have hproj : IsStarProjection (Theses.A.VN.floor (suPredVal p)) :=
      Theses.B.Dils.cornerSet.proj (Theses.A.VN.floor (suPredVal p))
    refine ⟨_, π, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · -- `π ∘ p = π ∘ 1`
      refine su_pred_ext (Eq.trans (suPredVal_comp π p)
        (Eq.trans ?_ (suPredVal_comp π (truth X)).symm))
      rw [suPredVal_truth X, hπ, hπ]
      exact hcorner
    · intro Z g hg
      -- `g(a) = g(1)`
      have hga : g.unop.toNCPMap (suPredVal p) = g.unop.toNCPMap 1 := by
        have h1 := congrArg suPredVal hg
        rwa [suPredVal_comp, suPredVal_comp, suPredVal_truth X] at h1
      obtain ⟨f', hf', huniq⟩ := huniv Z.unop.base.carrier _ _ _
        g.unop.toNCPMap hga
      have hsub : Theses.Subunital ⇑f' := by
        show f' 1 ≤ 1
        have h1 : f' (1 : Theses.B.Dils.cornerSet X.unop.base.carrier
            (Theses.A.VN.floor (suPredVal p))) = g.unop.toNCPMap 1 :=
          (congrArg (fun z => f' z) hunital.symm).trans (hf' 1)
        rw [h1]
        exact g.unop.subunital'
      obtain ⟨g', hg'⟩ : ∃ g' : Z ⟶ Opposite.op (WStarCPSU.of (WStar.of
            (Theses.B.Dils.cornerSet X.unop.base.carrier
              (Theses.A.VN.floor (suPredVal p))))),
          ∀ c, g'.unop.toNCPMap c = f' c :=
        ⟨Quiver.Hom.op ⟨f', hsub⟩, fun _ => rfl⟩
      refine ⟨g', suop_hom_ext fun x => ?_, fun k hk => ?_⟩
      · exact (suop_comp_apply g' π x).trans
          ((congrArg g'.unop.toNCPMap (hπ x)).trans ((hg' (h x)).trans (hf' x)))
      · have hk' : ∀ x, k.unop.toNCPMap (h x) = g.unop.toNCPMap x := by
          intro x
          refine Eq.trans (congrArg k.unop.toNCPMap (hπ x)).symm ?_
          exact (suop_comp_apply k π x).symm.trans
            (congrArg (fun m : Z ⟶ X => m.unop.toNCPMap x) hk)
        have hkf : k.unop.toNCPMap = f' := huniq k.unop.toNCPMap hk'
        exact suop_hom_ext fun c =>
          (congrArg (fun m => m c) hkf).trans (hg' c).symm
    · -- the carrier of the standard corner is `⌊a⌋`
      refine Theses.A.VN.carrier_eq _ _ hproj ?_ ?_
      · -- `⌊a⌋(1 − ⌊a⌋)⌊a⌋ = 0`
        have hz : π.unop.toNCPMap (1 - Theses.A.VN.floor (suPredVal p)) = 0 := by
          refine Theses.B.Dils.cornerSet.val_injective ?_
          rw [hπ, hval, mul_sub, mul_one, hproj.isIdempotentElem.eq, sub_self,
            zero_mul]
          rfl
        exact hz
      · intro q hq hq0
        -- `⌊a⌋(1 − q)⌊a⌋ = 0` forces `√(1−q)⌊a⌋ = 0`, hence `⌊a⌋ ≤ q`
        have hq0'' : π.unop.toNCPMap (1 - q) = 0 := hq0
        have hq0' : Theses.A.VN.floor (suPredVal p) * (1 - q)
            * Theses.A.VN.floor (suPredVal p) = 0 := by
          rw [← hval, ← hπ, hq0'']
          rfl
        have hqnn : (0 : X.unop.base.carrier) ≤ 1 - q := sub_nonneg.mpr hq.le_one
        have hsq : star (CFC.sqrt (1 - q) * Theses.A.VN.floor (suPredVal p))
            * (CFC.sqrt (1 - q) * Theses.A.VN.floor (suPredVal p)) = 0 := by
          rw [star_mul, hproj.isSelfAdjoint.star_eq,
            (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 - q))).star_eq]
          calc Theses.A.VN.floor (suPredVal p) * CFC.sqrt (1 - q)
                * (CFC.sqrt (1 - q) * Theses.A.VN.floor (suPredVal p))
              = Theses.A.VN.floor (suPredVal p)
                  * (CFC.sqrt (1 - q) * CFC.sqrt (1 - q))
                  * Theses.A.VN.floor (suPredVal p) := by noncomm_ring
            _ = 0 := by rw [CFC.sqrt_mul_sqrt_self _ hqnn]; exact hq0'
        have h1 : CFC.sqrt (1 - q) * Theses.A.VN.floor (suPredVal p) = 0 :=
          (CStarRing.star_mul_self_eq_zero_iff _).mp hsq
        have h2 : (1 - q) * Theses.A.VN.floor (suPredVal p) = 0 :=
          (Theses.A.VN.sqrt_mul_eq_zero_iff hqnn _).mp h1
        have h3 : Theses.A.VN.floor (suPredVal p) * (1 - q) = 0 := by
          have h4 := congrArg star h2
          rwa [star_mul, hproj.isSelfAdjoint.star_eq,
            hq.one_sub.isSelfAdjoint.star_eq, star_zero] at h4
        exact (Theses.A.VN.le_proj_iff ⟨hproj.nonneg, hproj.le_one⟩ hq).mpr h3
    · -- the standard corner is **surjective**: `h(y) = y` for `y` in `⌊a⌋𝒜⌊a⌋`
      intro y
      refine ⟨y.1, ?_⟩
      rw [hπ]
      refine Theses.B.Dils.cornerSet.val_injective ?_
      rw [hval]
      exact y.2
    · -- `⌊a⌋𝒜⌊a⌋` is commutative when `𝒜` is: its product is that of `𝒜`
      intro hX x y
      refine Theses.B.Dils.cornerSet.val_injective ?_
      exact hX _ _

/-- **199V at `vNᵒᵖ`** (eff.tex:3933, Examples): `vN_cpsuᵒᵖ` **has
comprehension**, and a comprehension for the effect `a` is the standard
corner `h_a : 𝒜 → ⌊a⌋𝒜⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋` (dils.tex 169IV
`standard_corner_dils`). -/
theorem su_hasComprehension : HasComprehension (WStarCPSU.{u}ᵒᵖ) :=
  ⟨fun p => by
    obtain ⟨W, π, hπ, -, -, -⟩ := su_exists_corner p
    exact ⟨W, π, hπ⟩⟩

/-- The standard filter `c_{aᗮ} : ⌈aᗮ⌉𝒜⌈aᗮ⌉ → 𝒜`, `b ↦ √(aᗮ) b √(aᗮ)`
(dils.tex 169X `dils_stand_filter`), as a quotient, together with the one
further fact the commutative subcategory `CvNᵒᵖ` of 206III needs of it: the
corner `⌈aᗮ⌉𝒜⌈aᗮ⌉` is commutative whenever `𝒜` is, because its
multiplication is that of `𝒜`.  `su_hasQuotients` below is the bare
197IV. -/
private theorem su_exists_filter {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃ (Q : WStarCPSU.{u}ᵒᵖ) (ξ : X ⟶ Q), IsQuotient p ξ ∧
      ((∀ x y : X.unop.base.carrier, x * y = y * x) →
        ∀ x y : Q.unop.base.carrier, x * y = y * x) := by
    have hb0 : (0 : X.unop.base.carrier) ≤ suPredVal (EffectusPartialForm.orth p) :=
      suPredVal_nonneg _
    obtain ⟨c, hcval, -, hc1, huniv⟩ := Theses.B.Dils.dils_stand_filter
      (B := X.unop.base.carrier) (suPredVal (EffectusPartialForm.orth p)) hb0
    letI : Theses.VonNeumannAlgebra
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.ceil (suPredVal (EffectusPartialForm.orth p)))) :=
      Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
    obtain ⟨ξ, hξ⟩ : ∃ ξ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of
          (Theses.B.Dils.cornerSet X.unop.base.carrier
            (Theses.A.VN.ceil (suPredVal (EffectusPartialForm.orth p)))))),
        ∀ x, ξ.unop.toNCPMap x = c x :=
      ⟨Quiver.Hom.op ⟨c, le_trans hc1 (suPredVal_le_one _)⟩, fun _ => rfl⟩
    refine ⟨_, ξ, ⟨?_, ?_⟩, ?_⟩
    · -- `1 ∘ ξ ≼ pᗮ`
      refine (su_pred_le_iff _ _).mpr ?_
      rw [suPredVal_comp, hξ, suPredVal_truth]
      exact hc1
    · intro Y f hf
      have hf1 : f.unop.toNCPMap (1 : Y.unop.base.carrier)
          ≤ suPredVal (EffectusPartialForm.orth p) := by
        have h1 := (su_pred_le_iff (f ≫ truth Y) (EffectusPartialForm.orth p)).mp hf
        rwa [suPredVal_comp, suPredVal_truth] at h1
      obtain ⟨f', hf', huniq⟩ := huniv Y.unop.base.carrier _ _ _
        f.unop.toNCPMap hf1
      obtain ⟨g, hg⟩ : ∃ g : Opposite.op (WStarCPSU.of (WStar.of
            (Theses.B.Dils.cornerSet X.unop.base.carrier
              (Theses.A.VN.ceil (suPredVal (EffectusPartialForm.orth p)))))) ⟶ Y,
          ∀ y, g.unop.toNCPMap y = f'.toNCPMap y :=
        ⟨Quiver.Hom.op f', fun _ => rfl⟩
      refine ⟨g, suop_hom_ext fun y => ?_, fun k hk => ?_⟩
      · exact (suop_comp_apply ξ g y).trans
          ((congrArg (fun z => ξ.unop.toNCPMap z) (hg y)).trans
            ((hξ (f'.toNCPMap y)).trans (hf' y)))
      · have hk' : ∀ y, c (k.unop.toNCPMap y) = f.unop.toNCPMap y := by
          intro y
          refine Eq.trans (hξ (k.unop.toNCPMap y)).symm ?_
          exact (suop_comp_apply ξ k y).symm.trans
            (congrArg (fun m : X ⟶ Y => m.unop.toNCPMap y) hk)
        have hkf : k.unop = f' := huniq k.unop hk'
        exact suop_hom_ext fun y =>
          (congrArg (fun m : Theses.NCPSUMap Y.unop.base.carrier _ =>
            m.toNCPMap y) hkf).trans (hg y).symm
    · -- `⌈aᗮ⌉𝒜⌈aᗮ⌉` is commutative when `𝒜` is: its product is that of `𝒜`
      intro hX x y
      refine Theses.B.Dils.cornerSet.val_injective ?_
      exact hX _ _

/-- **197IV at `vNᵒᵖ`** (eff.tex:3683, Examples): `vN_cpsuᵒᵖ` **has
quotients**, and a quotient for the effect `a` is the standard filter
`c_{aᗮ} : ⌈aᗮ⌉𝒜⌈aᗮ⌉ → 𝒜`, `b ↦ √(aᗮ) b √(aᗮ)` (dils.tex 169X
`dils_stand_filter`). -/
theorem su_hasQuotients : HasQuotients (WStarCPSU.{u}ᵒᵖ) where
  quot {X} p := by
    obtain ⟨Q, ξ, hξ, -⟩ := su_exists_filter p
    exact ⟨Q, ξ, hξ⟩

/-- **202IV at `vNᵒᵖ`** (eff.tex:4116, Examples): a predicate is *the*
image of `f` exactly when it names the carrier `⌈f⌉`. -/
private theorem su_isImage_carrier {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (q : Y ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (hq : suPredVal q = suCarrier f) :
    IsImage f q := by
  obtain ⟨-, hzero, -⟩ := su_carrier_spec f
  refine ⟨?_, ?_⟩
  · refine su_pred_ext (Eq.trans (suPredVal_comp f q)
      (Eq.trans ?_ (suPredVal_comp f (truth Y)).symm))
    rw [suPredVal_truth Y, hq]
    have hlin : f.unop.toNCPMap (1 - suCarrier f)
        = f.unop.toNCPMap 1 - f.unop.toNCPMap (suCarrier f) :=
      map_sub (ncpLin f.unop.toNCPMap) 1 (suCarrier f)
    rw [hlin] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · intro r hr
    refine (su_pred_le_iff q r).mpr ?_
    rw [hq]
    refine su_carrier_le f (suPredVal_nonneg r) (suPredVal_le_one r) ?_
    have h1 := congrArg suPredVal hr
    rwa [suPredVal_comp, suPredVal_comp, suPredVal_truth Y] at h1

/-- **202IV at `vNᵒᵖ`** (eff.tex:4116, Examples): `vN_cpsuᵒᵖ` **has
images**, and `im f` is the carrier `⌈f⌉` of vn.tex 63I. -/
theorem su_hasImages : HasImages (WStarCPSU.{u}ᵒᵖ) where
  im {X Y} f := by
    obtain ⟨hproj, -, -⟩ := su_carrier_spec f
    obtain ⟨q, hq⟩ := su_pred_exists (X := Y) hproj.nonneg hproj.le_one
    exact ⟨q, su_isImage_carrier f q hq⟩


/-- **202IV at `vNᵒᵖ`**, first half of the second sentence: a map of
`vN_cpsuᵒᵖ` is **faithful** (`im f = 1`, 202I.2) exactly when its carrier
`⌈f⌉` is `1`.  Immediate from `su_isImage_carrier`, which already says the
image is the carrier: one direction reads it at `q = 1` (`1` *is* `truth Y`,
`predEffectAlgebra`), the other feeds the minimality of `im f = 1` the
predicate naming `⌈f⌉`. -/
private theorem su_faithfulMap_iff_carrier {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    FaithfulMap f ↔ suCarrier f = 1 := by
  obtain ⟨hproj, -, -⟩ := su_carrier_spec f
  constructor
  · intro him
    obtain ⟨q, hq⟩ := su_pred_exists (X := Y) hproj.nonneg hproj.le_one
    have hle : (1 : Y ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) ≼ q :=
      him.2 q (su_isImage_carrier f q hq).1
    have h1 := (su_pred_le_iff _ _).mp hle
    rw [hq, show suPredVal (1 : Y ⟶ effObj (WStarCPSU.{u}ᵒᵖ))
      = (1 : Y.unop.base.carrier) from suPredVal_truth Y] at h1
    exact le_antisymm hproj.le_one h1
  · intro h
    refine su_isImage_carrier f (truth Y) ?_
    rw [suPredVal_truth Y, h]

/-- **202IV at `vNᵒᵖ`** (eff.tex:4116, Examples), SECOND sentence: *"the map
`f` is faithful if and only if `f(a*a) = 0` implies `a*a = 0` for all
`a ∈ 𝒜`."*  Here `f : X ⟶ Y` of `vN_cpsuᵒᵖ` is the ncpsu-map
`f.unop : 𝒜 → ℬ` with `𝒜 = Y.unop` — so `a` ranges over `Y.unop`, which is
where `im f = ⌈f⌉` lives.  eff.tex states this without proof.

Via `su_faithfulMap_iff_carrier` this is **63II.3** `carrier_basic_3`
(vn.tex:3054), which says `⌈f⌉ = 1` iff `f` kills no nonzero *positive*
element; `{a*a : a ∈ 𝒜}` is exactly the positive cone, and the direction
that needs the harder inclusion — a positive `b` is some `a*a` — is the one
that does not need it, because `b = 1 − ⌈f⌉` is a projection and hence
already of the form `a*a`. -/
theorem su_faithfulMap_iff {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    FaithfulMap f ↔ ∀ a : Y.unop.base.carrier,
      f.unop.toNCPMap (star a * a) = 0 → star a * a = 0 := by
  rw [su_faithfulMap_iff_carrier f]
  constructor
  · intro h a hfa
    exact (Theses.A.VN.carrier_basic_3 _ _).mp h _ (star_mul_self_nonneg a) hfa
  · intro h
    obtain ⟨hproj, hzero, -⟩ := su_carrier_spec f
    have hs : star ((1 : Y.unop.base.carrier) - suCarrier f)
        * (1 - suCarrier f) = 1 - suCarrier f :=
      (Theses.A.VN.isStarProjection_iff_star_mul_self _).mp hproj.one_sub
    have hz := h (1 - suCarrier f)
    rw [hs] at hz
    exact (sub_eq_zero.mp (hz hzero)).symm
/-- The floor of a projection is itself. -/
private theorem su_floor_of_isStarProjection {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] {z : A}
    (hz : IsStarProjection z) : Theses.A.VN.floor z = z := by
  rw [Theses.A.VN.floor_eq_one_sub_ceil ⟨hz.nonneg, hz.le_one⟩,
    Theses.A.VN.ceil_of_isStarProjection hz.one_sub, sub_sub_cancel]

/-- **203III at `vNᵒᵖ`** (eff.tex:4194, Example): **the sharp predicates of
`vNᵒᵖ` are exactly the projections.**  eff.tex states this without proof.
(⇒) an image is a carrier, and carriers are projections; (⇐) a projection
`z` is the image of the standard corner `h_z`, whose carrier is `⌊z⌋ = z`. -/
theorem su_isSharp_iff {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    IsSharp p ↔ IsStarProjection (suPredVal p) := by
  constructor
  · rintro ⟨Y, f, him⟩
    obtain ⟨hproj, -, -⟩ := su_carrier_spec f
    obtain ⟨q, hq⟩ := su_pred_exists (X := X) hproj.nonneg hproj.le_one
    have himq : IsImage f q := su_isImage_carrier f q hq
    have h1 : suPredVal p ≤ suPredVal q := (su_pred_le_iff p q).mp (him.2 q himq.1)
    have h2 : suPredVal q ≤ suPredVal p := (su_pred_le_iff q p).mp (himq.2 p him.1)
    rw [le_antisymm h1 h2, hq]
    exact hproj
  · intro hpr
    obtain ⟨W, π, -, hcar, -, -⟩ := su_exists_corner p
    exact ⟨W, π, su_isImage_carrier π p
      (by rw [hcar, su_floor_of_isStarProjection hpr])⟩

/-- **206II at `vNᵒᵖ`**: the orthocomplement of a sharp predicate is sharp —
the last axiom of a ⋄-effectus, and immediate from `su_isSharp_iff` because
`1 − z` is a projection whenever `z` is. -/
theorem su_orth_sharp {X : WStarCPSU.{u}ᵒᵖ}
    {s : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} (hs : IsSharp s) :
    IsSharp (EffectAlgebra.orth s) := by
  rw [su_isSharp_iff] at hs ⊢
  rw [show suPredVal (EffectAlgebra.orth s) = 1 - suPredVal s from suPredVal_orth s]
  exact hs.one_sub

/-- **206III at `vN_cpsuᵒᵖ`** (eff.tex:4460, Examples): `vN_cpsuᵒᵖ` is a
⋄-effectus. -/
theorem su_diamondEffectus : DiamondEffectus (WStarCPSU.{u}ᵒᵖ) :=
  { su_hasQuotients, su_hasComprehension, su_hasImages with
    orth_sharp := fun hs => su_orth_sharp hs }

/-- **210III at `vNᵒᵖ`** (`exa-sharp-vn`, eff.tex:4777, Example), the first
step: a map of `vN_cpsuᵒᵖ` is **sharp exactly when its ncpsu-map sends
projections to projections**.  This is Definition 210I unfolded at `vNᵒᵖ`;
the Example itself — *the sharp maps are exactly the mni-maps* — is
`su_sharpMap_iff_mni` below. -/
theorem su_sharpMap_iff {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    SharpMap f ↔ ∀ z : Y.unop.base.carrier, IsStarProjection z →
      IsStarProjection (f.unop.toNCPMap z) := by
  constructor
  · intro hf z hz
    obtain ⟨s, hs⟩ := su_pred_exists (X := Y) hz.nonneg hz.le_one
    have hsharp : IsSharp s := (su_isSharp_iff s).mpr (by rw [hs]; exact hz)
    have := (su_isSharp_iff (f ≫ s)).mp (hf s hsharp)
    rwa [suPredVal_comp, hs] at this
  · intro hf s hs
    refine (su_isSharp_iff (f ≫ s)).mpr ?_
    rw [suPredVal_comp]
    exact hf _ ((su_isSharp_iff s).mp hs)

/-! ### The sharp maps are the mni-maps (**210III**, eff.tex:4777, via **99XII**)

eff.tex:4778 reads, in full: *"In `vNᵒᵖ` the sharp maps are exactly the
mni-maps (i.e. the normal ∗-homomorphisms).  See `sharp-multiplicative`."*
**mni**, not nmiu: the ∗-homomorphism is **not** assumed unital, and in the
partial-form category this file works in the non-unital case is the general
one — a sharp map of `vN_cpsuᵒᵖ` need not be total.

The identification, in both directions and without unitality, is
`su_sharpMap_iff_mni`.  It is the Example's own route:

* `su_sharpMap_iff` above says a map of `vN_cpsuᵒᵖ` is sharp iff its
  ncpsu-map sends projections to projections (Definition 210I at `vNᵒᵖ`);
* the reference the Example gives, `sharp-multiplicative` = **99XII**
  (proc.tex:905), is `Theses.A.Proc.sharp_multiplicative`: for an *ncp*-map
  between von Neumann algebras, *sends projections to projections ⟺
  multiplicative*.  It needs **no** unitality — which is exactly why the
  Example can drop it — so `gardner` (99II), whose form does need it, is not
  called;
* involution preservation is `cstar_p_implies_i`, valid for any positive
  map; and normality is `preservesDirSups'`, carried along.

This is the one place in `B/Eff` that uses `Theses.A.Proc`.

`su_exists_nmiu_of_sharp_total` is then the *total* case — an mni-map whose
`ρ 1 = 1`, i.e. an **nmiu**-map — which is what the dilation theory of
221III and the two `A/Proc` bridges consume. -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- An nmiu-map is an ncpsu-map — indeed unital.  **34IV**.3 (`cp`,
cstar.tex:5448, Exercise) is the one ingredient — *an mi-map is completely
positive*, `cp_of_mi` — and this lemma repackages it, adding the normality
and the subunitality that the source does not mention. -/
theorem su_exists_ncpsu_of_nmiu {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : Theses.NMIUMap A B) :
    ∃ g : Theses.NCPSUMap A B, ∀ a, g.toNCPMap a = f a :=
  ⟨⟨{ toCompletelyPositiveMap :=
        { toLinearMap := (f.toStarAlgHom : A →ₐ[ℂ] B).toLinearMap
          map_cstarMatrix_nonneg' :=
            (cp_iff _).out 0 1 |>.mp
              (cp_of_mi _ (fun x y => map_mul f.toStarAlgHom x y)
                (fun x => map_star f.toStarAlgHom x)) }
      preservesDirSups' := f.preservesDirSups' },
    show (f.toStarAlgHom : A →ₐ[ℂ] B).toLinearMap 1 ≤ 1 by
      rw [show (f.toStarAlgHom : A →ₐ[ℂ] B).toLinearMap (1 : A) = (1 : B) from
        map_one f.toStarAlgHom]⟩, fun _ => rfl⟩

/-- **210III at `vNᵒᵖ`** (`exa-sharp-vn`, eff.tex:4777, Example), one half,
in the Example's own generality: the ncpsu-map of a **sharp** map of
`vN_cpsuᵒᵖ` is a **normal ∗-homomorphism** — an **mni**-map, *not* assumed
unital.

Multiplicativity is **99XII** `sharp_multiplicative` at the projections
supplied by `su_sharpMap_iff`; involution preservation is
`cstar_p_implies_i` for the positive map `f`; normality is the map's own
`preservesDirSups'`. -/
theorem su_exists_mni_of_sharp {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (hs : SharpMap f) :
    ∃ ρ : Y.unop.base.carrier →⋆ₙₐ[ℂ] X.unop.base.carrier,
      Theses.PreservesDirSups ρ ∧ ∀ a, ρ a = f.unop.toNCPMap a := by
  have hproj : ∀ z : Y.unop.base.carrier, IsStarProjection z →
      IsStarProjection (f.unop.toNCPMap z) := (su_sharpMap_iff f).mp hs
  have hmul : ∀ a b : Y.unop.base.carrier,
      f.unop.toNCPMap (a * b) = f.unop.toNCPMap a * f.unop.toNCPMap b :=
    ((Theses.A.Proc.sharp_multiplicative f.unop.toNCPMap).out 1 0).mp hproj
  have hstar : ∀ a : Y.unop.base.carrier,
      ncpLin f.unop.toNCPMap (star a) = star (ncpLin f.unop.toNCPMap a) :=
    cstar_p_implies_i (ncpLin f.unop.toNCPMap)
      (astara_pos_basic_2_cp _ (ncpLin_cp f.unop.toNCPMap))
  exact ⟨{ toFun := f.unop.toNCPMap
           map_smul' := (ncpLin f.unop.toNCPMap).map_smul
           map_zero' := (ncpLin f.unop.toNCPMap).map_zero
           map_add' := (ncpLin f.unop.toNCPMap).map_add
           map_mul' := hmul
           map_star' := hstar },
    f.unop.toNCPMap.preservesDirSups', fun _ => rfl⟩

/-- **210III at `vNᵒᵖ`**, the converse half: a map of `vN_cpsuᵒᵖ` whose
ncpsu-map is a ∗-homomorphism is sharp.  No unitality and no normality are
used: a ∗-homomorphism sends projections to projections
(`IsStarProjection.map`), which is `su_sharpMap_iff`. -/
theorem su_sharp_of_mni {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (ρ : Y.unop.base.carrier →⋆ₙₐ[ℂ] X.unop.base.carrier)
    (hρ : ∀ a, ρ a = f.unop.toNCPMap a) : SharpMap f := by
  refine (su_sharpMap_iff f).mpr fun z hz => ?_
  rw [← hρ z]
  exact hz.map ρ

/-- **210III** (`exa-sharp-vn`, eff.tex:4777, Example) at `vNᵒᵖ`, in full:
**the sharp maps of `vNᵒᵖ` are exactly the mni-maps** — the normal
∗-homomorphisms, *not* assumed unital.  (`ρ` runs over
`NonUnitalStarAlgHom`s, and `PreservesDirSups ρ` is the "n" of mni.) -/
theorem su_sharpMap_iff_mni {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    SharpMap f ↔ ∃ ρ : Y.unop.base.carrier →⋆ₙₐ[ℂ] X.unop.base.carrier,
      Theses.PreservesDirSups ρ ∧ ∀ a, ρ a = f.unop.toNCPMap a :=
  ⟨su_exists_mni_of_sharp f, fun ⟨ρ, _, hρ⟩ => su_sharp_of_mni f ρ hρ⟩

/-- **210III at `vNᵒᵖ`**, the **total** case: a sharp *total* map of
`vN_cpsuᵒᵖ` is an **nmiu**-map.  This is `su_exists_mni_of_sharp` plus
`su_isTotal_iff`, which turns totality into `ρ 1 = 1`; it is the form the
dilation theory below consumes. -/
theorem su_exists_nmiu_of_sharp_total {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (hs : SharpMap f) (ht : IsTotal f) :
    ∃ ρ : Theses.NMIUMap Y.unop.base.carrier X.unop.base.carrier,
      ∀ a, ρ a = f.unop.toNCPMap a := by
  obtain ⟨ρ₀, -, hρ₀⟩ := su_exists_mni_of_sharp f hs
  have hcoe : ∀ c : Y.unop.base.carrier, ncpLin f.unop.toNCPMap c = ρ₀ c :=
    fun c => (hρ₀ c).symm
  have hmul : ∀ a b : Y.unop.base.carrier,
      ncpLin f.unop.toNCPMap (a * b)
        = ncpLin f.unop.toNCPMap a * ncpLin f.unop.toNCPMap b := by
    intro a b
    simp only [hcoe]
    exact map_mul ρ₀ a b
  have hstar : ∀ a : Y.unop.base.carrier,
      ncpLin f.unop.toNCPMap (star a) = star (ncpLin f.unop.toNCPMap a) := by
    intro a
    simp only [hcoe]
    exact map_star ρ₀ a
  have hone : ncpLin f.unop.toNCPMap 1 = 1 := (su_isTotal_iff f).mp ht
  exact ⟨{ toStarAlgHom :=
             ⟨AlgHom.ofLinearMap (ncpLin f.unop.toNCPMap) hone hmul, hstar⟩
           preservesDirSups' := f.unop.toNCPMap.preservesDirSups' }, fun _ => rfl⟩

/-- The converse of `su_exists_nmiu_of_sharp_total`: a map whose ncpsu-map
is an nmiu-map is sharp and total. -/
theorem su_sharp_total_of_nmiu {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (ρ : Theses.NMIUMap Y.unop.base.carrier X.unop.base.carrier)
    (hρ : ∀ a, ρ a = f.unop.toNCPMap a) : SharpMap f ∧ IsTotal f := by
  constructor
  · refine (su_sharpMap_iff f).mpr fun z hz => ?_
    rw [← hρ z]
    exact hz.map ρ.toStarAlgHom
  · refine (su_isTotal_iff f).mpr ?_
    rw [← hρ 1]
    exact map_one ρ.toStarAlgHom

/-! ### Filters are quotients, and *unital* corners are comprehensions

`su_hasQuotients` and `su_hasComprehension` above produce **one** quotient
and **one** comprehension per predicate, from the standard filter and the
standard corner.  `IsPure` needs the dictionary read in the other direction:
an *arbitrary* filter is a quotient, and an arbitrary *unital* corner is a
comprehension.  Both are the definitions of `IsFilterFor`/`IsCornerFor`
(dils.tex 169VIII, 169II) transported through `suPredVal`, and the two
mismatches are the ones the section header above records: `IsFilterFor`'s
mediating map is subunital (the author's ruling of 2026-08-16, the
**169VIII** row of `ERRATA.md`), which is exactly a morphism, and
`IsCornerFor`'s is merely ncp, which is a morphism only because the corner
is unital.

**Unitality of the corner is a real hypothesis, not a convenience.**  Under
169II as printed, `λ·h_a` is again a corner for `a` when `0 < λ < 1`
(QUESTIONS **D7**), and then the mediating map of a *subunital* `f` is
`λ⁻¹·f'`, which need not be subunital; such a corner is therefore not a
comprehension.  Every corner used below is unital, being the right leg of a
Paschke dilation of a unital map.

It is also **not a strengthening of 199V**.  199V's "comprehensions are
exactly the same thing as corners" cites `\sref{corner}` = proc.tex 95I,
which states in terms: *"When we write 'corner' we shall always mean a
'unital corner' unless explicitly stated otherwise"* (proc.tex:280).  So the
`hu` hypothesis below is the printed notion of corner, and the Example's
"exactly the same thing" is `su_isComprehension_iff_isCornerMap`. -/

/-- **197IV at `vNᵒᵖ`**, the converse reading of `su_hasQuotients`: a map
`ξ : X ⟶ Q` whose ncpsu-map is a **filter** for the effect named by `pᗮ` is
a quotient for `p`. -/
theorem su_isQuotient_of_isFilterFor {X Q : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (ξ : X ⟶ Q)
    (hf : Theses.B.Dils.IsFilterFor ξ.unop.toNCPMap
      (suPredVal (EffectusPartialForm.orth p))) :
    IsQuotient p ξ := by
  obtain ⟨-, hc1, huniv⟩ := hf
  constructor
  · refine (su_pred_le_iff _ _).mpr ?_
    rw [suPredVal_comp, suPredVal_truth]
    exact hc1
  · intro Y f hfle
    have hf1 : f.unop.toNCPMap (1 : Y.unop.base.carrier)
        ≤ suPredVal (EffectusPartialForm.orth p) := by
      have h1 := (su_pred_le_iff (f ≫ truth Y) (EffectusPartialForm.orth p)).mp hfle
      rwa [suPredVal_comp, suPredVal_truth] at h1
    obtain ⟨f', hf', huniq⟩ :=
      huniv Y.unop.base.carrier _ _ _ f.unop.toNCPMap hf1
    obtain ⟨g, hg⟩ : ∃ g : Q ⟶ Y, ∀ y, g.unop.toNCPMap y = f'.toNCPMap y :=
      ⟨Quiver.Hom.op f', fun _ => rfl⟩
    refine ⟨g, suop_hom_ext fun y => ?_, fun k hk => ?_⟩
    · exact (suop_comp_apply ξ g y).trans
        ((congrArg (fun z => ξ.unop.toNCPMap z) (hg y)).trans (hf' y))
    · have hk' : ∀ y, ξ.unop.toNCPMap (k.unop.toNCPMap y) = f.unop.toNCPMap y :=
        fun y => (suop_comp_apply ξ k y).symm.trans
          (congrArg (fun m : X ⟶ Y => m.unop.toNCPMap y) hk)
      have hkf : k.unop = f' := huniq k.unop hk'
      exact suop_hom_ext fun y =>
        (congrArg (fun m : Theses.NCPSUMap Y.unop.base.carrier Q.unop.base.carrier =>
          m.toNCPMap y) hkf).trans (hg y).symm

/-- **199V at `vNᵒᵖ`**, the converse reading of `su_hasComprehension`: a map
`π : W ⟶ X` whose ncpsu-map is a **unital corner** for the effect named by
`q` is a comprehension for `q`. -/
theorem su_isComprehension_of_isCornerFor {W X : WStarCPSU.{u}ᵒᵖ}
    (q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (π : W ⟶ X)
    (hu : π.unop.toNCPMap (1 : X.unop.base.carrier) = (1 : W.unop.base.carrier))
    (hc : Theses.B.Dils.IsCornerFor π.unop.toNCPMap (suPredVal q)) :
    IsComprehension q π := by
  obtain ⟨-, hval, huniv⟩ := hc
  constructor
  · refine su_pred_ext ?_
    rw [suPredVal_comp, suPredVal_comp, suPredVal_truth]
    exact hval
  · intro Z g hgq
    have hgval : g.unop.toNCPMap (suPredVal q)
        = g.unop.toNCPMap (1 : X.unop.base.carrier) := by
      have h1 := congrArg suPredVal hgq
      rwa [suPredVal_comp, suPredVal_comp, suPredVal_truth] at h1
    obtain ⟨f', hf', huniq⟩ :=
      huniv Z.unop.base.carrier _ _ _ g.unop.toNCPMap hgval
    have hsub : f' (1 : W.unop.base.carrier) ≤ 1 := by
      have h := hf' (1 : X.unop.base.carrier)
      rw [hu] at h
      rw [h]
      exact g.unop.subunital'
    obtain ⟨g', hgg⟩ : ∃ g' : Z ⟶ W, ∀ x, g'.unop.toNCPMap x = f' x :=
      ⟨Quiver.Hom.op ⟨f', hsub⟩, fun _ => rfl⟩
    refine ⟨g', suop_hom_ext fun x => ?_, fun k hk => ?_⟩
    · exact (suop_comp_apply g' π x).trans ((hgg _).trans (hf' x))
    · have hk' : ∀ x, k.unop.toNCPMap (π.unop.toNCPMap x) = g.unop.toNCPMap x :=
        fun x => (suop_comp_apply k π x).symm.trans
          (congrArg (fun m : Z ⟶ X => m.unop.toNCPMap x) hk)
      have hkf : k.unop.toNCPMap = f' := huniq k.unop.toNCPMap hk'
      exact suop_hom_ext fun x =>
        (congrArg (fun m : Theses.NCPMap W.unop.base.carrier Z.unop.base.carrier =>
          m x) hkf).trans (hgg x).symm

/-! ### Dilations are Paschke dilations (221III)

eff.tex:6806 says only "as shown in `existence-paschke`", and the two
statements are the same one *only* after the identifications above: the
abstract universal property of 221II quantifies over **sharp total** maps
`ϱ'` where **140II** `def-paschke` quantifies over **nmiu**-maps, and its
`h` is asked to be **pure** where the Paschke triple asks nothing of it.
`su_exists_nmiu_of_sharp_total` closes the first gap and
`su_isQuotient_of_isFilterFor`/`su_isComprehension_of_isCornerFor` the
second.  Two further mismatches are harmless and worth recording:

* the mediating map of **140II** is an arbitrary ncp-map where a morphism of
  `vN_cpsuᵒᵖ` must be subunital — but it is *unital*, because
  `σ(1) = σ(ϱ'(1)) = ϱ(1) = 1`, both legs being nmiu;
* uniqueness in **140II** is among all ncp-maps, which is stronger than the
  uniqueness the effectus asks for.

`su_isDilation_of_paschke` is the translation; `su_hasDilations` is the
construction it is fed.  Note that the dilation used is **not** the Paschke
dilation of `φ` taken straight from `existence_paschke`: `IsPure` needs a
*unital* corner, so the dilation is assembled the way **170II**.2 assembles
it — filter off `φ(1)` first (`dils_filter_basics_2a`), dilate the resulting
*unital* `φ'`, and put the filter back (`dils_filter_basics_2b`).  The right
leg of a dilation of a unital map is a corner (**169V**) and is unital,
`h(1) = h(ϱ(1)) = φ'(1) = 1`. -/

private theorem su_isDilation_of_paschke {X Y P Q : WStarCPSU.{u}ᵒᵖ}
    (f : X ⟶ Y) (ϱ : P ⟶ Y) (ξ : X ⟶ Q) (π : Q ⟶ P)
    (ρ : Theses.NMIUMap Y.unop.base.carrier P.unop.base.carrier)
    (hρ : ∀ a, ρ a = ϱ.unop.toNCPMap a)
    (hfilter : Theses.B.Dils.IsFilterFor ξ.unop.toNCPMap
      (f.unop.toNCPMap (1 : Y.unop.base.carrier)))
    (hπu : π.unop.toNCPMap (1 : P.unop.base.carrier) = (1 : Q.unop.base.carrier))
    (hcorner : Theses.B.Dils.IsCorner π.unop.toNCPMap)
    (hh : Theses.NCPMap P.unop.base.carrier X.unop.base.carrier)
    (hhval : ∀ x, hh x = (ξ ≫ π).unop.toNCPMap x)
    (hdil : Theses.B.Dils.IsPaschkeDilationOf
      ⟨P.unop.base.carrier, inferInstance, ρ, hh⟩ ⇑f.unop.toNCPMap) :
    IsDilation f ϱ (ξ ≫ π) := by
  obtain ⟨hfac0, huniv⟩ := hdil
  have hfac : ∀ a, (ξ ≫ π).unop.toNCPMap (ρ a) = f.unop.toNCPMap a :=
    fun a => (hhval _).symm.trans (hfac0 a)
  obtain ⟨hsharp, htotal⟩ := su_sharp_total_of_nmiu ϱ ρ hρ
  have hρ1 : ρ (1 : Y.unop.base.carrier) = (1 : P.unop.base.carrier) :=
    map_one ρ.toStarAlgHom
  refine ⟨hsharp, htotal, ?_, ?_, ?_⟩
  · -- `ξ ≫ π` is pure: a filter after a unital corner
    obtain ⟨a, hca⟩ := hcorner
    obtain ⟨q, hq⟩ := su_pred_exists (X := P) hca.1.1 hca.1.2
    obtain ⟨p, hp⟩ := su_pred_exists (X := X)
      (a := 1 - f.unop.toNCPMap (1 : Y.unop.base.carrier))
      (sub_nonneg.mpr f.unop.subunital') (sub_le_self 1 (ncpsu_one_nonneg f.unop))
    refine ⟨Q, ξ, π, p, q, su_isQuotient_of_isFilterFor p ξ ?_,
      su_isComprehension_of_isCornerFor q π hπu ?_, rfl⟩
    · rw [show suPredVal (EffectusPartialForm.orth p)
          = f.unop.toNCPMap (1 : Y.unop.base.carrier) by
        rw [suPredVal_orth, hp, sub_sub_cancel]]
      exact hfilter
    · rw [hq]; exact hca
  · -- `(ξ ≫ π) ≫ ϱ = f`
    refine suop_hom_ext fun a => ?_
    refine Eq.trans (suop_comp_apply (ξ ≫ π) ϱ a) ?_
    rw [← hρ a]
    exact hfac a
  · -- the universal property
    intro P' ϱ' h' hs' ht' hfac'
    obtain ⟨ρ', hρ'⟩ := su_exists_nmiu_of_sharp_total ϱ' hs' ht'
    have hρ'1 : ρ' (1 : Y.unop.base.carrier) = (1 : P'.unop.base.carrier) :=
      map_one ρ'.toStarAlgHom
    obtain ⟨σ, ⟨hσρ, hσh⟩, hσu⟩ :=
      huniv ⟨P'.unop.base.carrier, inferInstance, ρ', h'.unop.toNCPMap⟩
        (fun a => by
          refine Eq.trans (congrArg (fun z => h'.unop.toNCPMap z) (hρ' a)) ?_
          exact (suop_comp_apply h' ϱ' a).symm.trans
            (congrArg (fun m : X ⟶ Y => m.unop.toNCPMap a) hfac'))
    have hσ1 : σ (1 : P'.unop.base.carrier) ≤ (1 : P.unop.base.carrier) := by
      have h := hσρ (1 : Y.unop.base.carrier)
      rw [hρ'1, hρ1] at h
      exact le_of_eq h
    obtain ⟨s, hs⟩ : ∃ s : P ⟶ P', ∀ x, s.unop.toNCPMap x = σ x :=
      ⟨Quiver.Hom.op ⟨σ, hσ1⟩, fun _ => rfl⟩
    refine ⟨s, ⟨suop_hom_ext fun c => ?_, suop_hom_ext fun a => ?_⟩, ?_⟩
    · exact (suop_comp_apply (ξ ≫ π) s c).trans
        ((congrArg (fun z => (ξ ≫ π).unop.toNCPMap z) (hs c)).trans
          ((hhval _).symm.trans (hσh c)))
    · refine Eq.trans (suop_comp_apply s ϱ' a) ?_
      refine Eq.trans (hs _) ?_
      refine Eq.trans (congrArg (fun z => σ z) (hρ' a).symm) ?_
      exact (hσρ a).trans (hρ a)
    · rintro k ⟨hk1, hk2⟩
      have hk1' : ∀ c, hh (k.unop.toNCPMap c) = h'.unop.toNCPMap c := fun c =>
        (hhval _).trans ((suop_comp_apply (ξ ≫ π) k c).symm.trans
          (congrArg (fun m : X ⟶ P' => m.unop.toNCPMap c) hk1))
      have hk2' : ∀ a, k.unop.toNCPMap (ρ' a) = ρ a := fun a =>
        ((congrArg (fun z => k.unop.toNCPMap z) (hρ' a)).trans
          ((suop_comp_apply k ϱ' a).symm.trans
            (congrArg (fun m : P ⟶ Y => m.unop.toNCPMap a) hk2))).trans (hρ a).symm
      have hkσ : k.unop.toNCPMap = σ := hσu k.unop.toNCPMap ⟨hk2', hk1'⟩
      exact suop_hom_ext fun x =>
        (congrArg (fun m : Theses.NCPMap P'.unop.base.carrier P.unop.base.carrier =>
          m x) hkσ).trans (hs x).symm

/-- **221III at `vN_cpsuᵒᵖ`** (eff.tex:6805, Example): **`vNᵒᵖ` has
dilations** — the Paschke dilations of **154III**. -/
theorem su_hasDilations (hDia : DiamondEffectus (WStarCPSU.{u}ᵒᵖ)) :
    letI := hDia
    HasDilations (WStarCPSU.{u}ᵒᵖ) := by
  letI := hDia
  refine ⟨?_⟩
  intro X Y f
  have hb : (0 : X.unop.base.carrier)
      ≤ f.unop.toNCPMap (1 : Y.unop.base.carrier) := ncpsu_one_nonneg f.unop
  -- **169X**: the standard filter for `φ(1)`, kept as an opaque algebra `C'`
  obtain ⟨C', iC, iP, iS, iV, c', hc'⟩ :
      ∃ (C' : Type u) (_ : CStarAlgebra C') (_ : PartialOrder C')
        (_ : StarOrderedRing C') (_ : Theses.VonNeumannAlgebra C')
        (c' : Theses.NCPMap C' X.unop.base.carrier),
        Theses.B.Dils.IsFilterFor c'
          (f.unop.toNCPMap (1 : Y.unop.base.carrier)) := by
    letI : Theses.VonNeumannAlgebra
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.ceil (f.unop.toNCPMap (1 : Y.unop.base.carrier)))) :=
      Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
    obtain ⟨c, -, hc⟩ := Theses.B.Dils.dils_stand_filter
      (f.unop.toNCPMap (1 : Y.unop.base.carrier)) hb
    exact ⟨_, _, _, _, inferInstance, c, hc⟩
  letI := iC; letI := iP; letI := iS; letI := iV
  -- **169XI**.2a: the unique *unital* `φ'` with `φ = c' ∘ φ'`
  obtain ⟨φ', ⟨hφ'1, hφ'2⟩, -⟩ :=
    Theses.B.Dils.dils_filter_basics_2a f.unop.toNCPMap c' hc'
  -- **154III**: a Paschke dilation of `φ'`
  obtain ⟨M⟩ := Theses.B.Dils.existence_paschke φ'
  obtain ⟨D, hDil⟩ : ∃ D : Theses.B.Dils.PaschkeTriple Y.unop.base.carrier C',
      Theses.B.Dils.IsPaschkeDilationOf D ⇑φ' :=
    ⟨_, Theses.B.Dils.existence_paschke_5 φ' M⟩
  letI := D.vn
  have hρ1 : D.ρ (1 : Y.unop.base.carrier) = (1 : D.P) := map_one D.ρ.toStarAlgHom
  -- the right leg of a dilation of a *unital* map is a **unital** corner (169V)
  have hDh1 : D.h (1 : D.P) = 1 := by
    have h := hDil.1 (1 : Y.unop.base.carrier)
    rw [hρ1, hφ'1] at h
    exact h
  have hcorner := Theses.B.Dils.h_is_corner_for_unital_map φ' hφ'1 D hDil
  -- **169XI**.2b: putting the filter back gives a Paschke dilation of `φ`
  obtain ⟨h₂, hh₂, hD₂⟩ := Theses.B.Dils.dils_filter_basics_2b
    f.unop.toNCPMap c' hc' φ' ⟨hφ'1, hφ'2⟩ D hDil
  -- the objects and the three morphisms of `vN_cpsuᵒᵖ`
  obtain ⟨g, hg⟩ := su_exists_ncpsu_of_nmiu D.ρ
  obtain ⟨ϱ, hϱ⟩ : ∃ ϱ : Opposite.op (WStarCPSU.of (WStar.of D.P)) ⟶ Y,
      ∀ a, ϱ.unop.toNCPMap a = g.toNCPMap a := ⟨Quiver.Hom.op g, fun _ => rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of C')),
      ξ.unop.toNCPMap = c' :=
    ⟨Quiver.Hom.op ⟨c', le_trans hc'.2.1 f.unop.subunital'⟩, rfl⟩
  obtain ⟨π, hπ⟩ : ∃ π : Opposite.op (WStarCPSU.of (WStar.of C')) ⟶
        Opposite.op (WStarCPSU.of (WStar.of D.P)),
      π.unop.toNCPMap = D.h :=
    ⟨Quiver.Hom.op ⟨D.h, le_of_eq hDh1⟩, rfl⟩
  refine ⟨_, ϱ, ξ ≫ π, su_isDilation_of_paschke f ϱ ξ π D.ρ
    (fun a => ((hϱ a).trans (hg a)).symm) ?_ ?_ ?_ h₂ ?_ ?_⟩
  · rw [hξ]; exact hc'
  · rw [hπ]; exact hDh1
  · rw [hπ]; exact hcorner
  · intro x
    refine Eq.trans (hh₂ x) ?_
    refine Eq.trans ?_ (suop_comp_apply ξ π x).symm
    rw [hξ, hπ]
    rfl
  · exact hD₂

/-! ### The assert maps of `vNᵒᵖ` (211II at `vNᵒᵖ`, eff.tex:4859)

`asrt_p` is characterised (**211II**) as the unique **⋄-positive** map with
`1 ∘ asrt_p = p`, and 206II.4 defines ⋄-positive as *pure and of the form
`g ∘ g` for a ⋄-self-adjoint `g`*.  So identifying `asrt_p` in `vNᵒᵖ` as
`ad_{√a} : b ↦ √a b √a` needs both halves, and the ⋄ half needs `f^⋄` and
`f_⋄` computed here.

**`f_⋄` never has to be computed.**  By **207III** `diamond_adjunction`,
`f^⋄(s) ≤ tᵖ ⟺ f_⋄(t) ≤ sᵖ`; so if `f^⋄` is *symmetric* in the sense that
`f^⋄(s) ≤ tᵖ ⟺ f^⋄(t) ≤ sᵖ`, then `f_⋄(t)` and `f^⋄(t)` have the same
`ᵖ`-upper bounds and `f` is ⋄-self-adjoint (`su_diamondSelfAdjoint_of_symm`).
And `f^⋄` *is* computable from the dictionary alone: `f^⋄(s) = ⌈f(z)⌉` where
`z` is the projection naming `s`.  For `f = ad_w` the condition becomes
`y w z w = 0 ⟺ z w y w = 0` for projections `y, z`, which is
`(zwy)^* = ywz` — three lines of C\*-algebra, and no comprehension map,
image or corner algebra appears anywhere. -/

section DiaVN

variable [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **203III at `vNᵒᵖ`**: the ceiling of predicates is the ceiling `⌈·⌉` of
vn.tex 59I.  Both are least among projections above the effect
(`ceil_le_iff_of_isSharp` and `ceil_basic_1`, through `su_isSharp_iff`). -/
theorem su_ceilPred_val {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    suPredVal (ceilPred p) = Theses.A.VN.ceil (suPredVal p) := by
  have hp0 : (0 : X.unop.base.carrier) ≤ suPredVal p := suPredVal_nonneg p
  have hp1 : suPredVal p ≤ 1 := suPredVal_le_one p
  have hcproj : IsStarProjection (suPredVal (ceilPred p)) :=
    (su_isSharp_iff _).mp (isSharp_ceil p)
  have hceilproj : IsStarProjection (Theses.A.VN.ceil (suPredVal p)) :=
    (Theses.A.VN.ceil_spec hp0).1
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hq⟩ := su_pred_exists (X := X) hceilproj.nonneg hceilproj.le_one
    have hsq : IsSharp q := (su_isSharp_iff q).mpr (by rw [hq]; exact hceilproj)
    have hpq : p ≼ q := by
      refine (su_pred_le_iff p q).mpr ?_
      rw [hq]
      refine (Theses.A.VN.le_proj_iff ⟨hp0, hp1⟩ hceilproj).mpr ?_
      rw [mul_sub, mul_one, (Theses.A.VN.ceil_spec hp0).2.1, sub_self]
    have hle := (su_pred_le_iff (ceilPred p) q).mp
      ((ceil_le_iff_of_isSharp hsq).mpr hpq)
    rwa [hq] at hle
  · refine (Theses.A.VN.ceil_le_iff hp0 hcproj).mpr ?_
    have hle : suPredVal p ≤ suPredVal (ceilPred p) :=
      (su_pred_le_iff p (ceilPred p)).mp (le_ceil p)
    have h := (Theses.A.VN.le_proj_iff ⟨hp0, hp1⟩ hcproj).mp hle
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm

/-- `f^⋄` in `vN_cpsuᵒᵖ`: the sharp predicate `f^⋄(s)` names the carrier
`⌈f(z)⌉` of the image of the projection `z` naming `s`. -/
theorem su_diaPull_val {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (s : SPred Y) :
    suPredVal (diaPull f s).1
      = Theses.A.VN.ceil (f.unop.toNCPMap (suPredVal s.1)) := by
  show suPredVal (ceilPred (f ≫ s.1)) = _
  rw [su_ceilPred_val, suPredVal_comp]

/-- A ⋄-self-adjointness criterion that never mentions `f_⋄`: by **207III**
`diamond_adjunction` it is enough that `f^⋄` be symmetric. -/
theorem su_diamondSelfAdjoint_of_symm {X : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ X)
    (hsymm : ∀ s t : SPred X, (diaPull f s).1 ≼ EffectAlgebra.orth t.1 ↔
      (diaPull f t).1 ≼ EffectAlgebra.orth s.1) :
    DiamondSelfAdjoint f := by
  show diaPull f = diaPush f
  refine funext fun t => Subtype.ext (eabasics_le_antisymm ?_ ?_)
  · have h0 : (diaPush f t).1 ≼ EffectAlgebra.orth ((diaPush f t).orth).1 := by
      rw [spred_orth_val, eabasics_orth_orth]
      exact pcm_preorder_refl _
    have h2 := (hsymm (diaPush f t).orth t).mp
      ((diamond_adjunction f (diaPush f t).orth t).mpr h0)
    rw [spred_orth_val, eabasics_orth_orth] at h2
    exact h2
  · have h0 : (diaPull f t).1 ≼ EffectAlgebra.orth ((diaPull f t).orth).1 := by
      rw [spred_orth_val, eabasics_orth_orth]
      exact pcm_preorder_refl _
    have h2 := (diamond_adjunction f (diaPull f t).orth t).mp
      ((hsymm t (diaPull f t).orth).mp h0)
    rw [spred_orth_val, eabasics_orth_orth] at h2
    exact h2

end DiaVN


omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- The C\*-content of ⋄-self-adjointness of `ad_w`: for projections `y, z`
and self-adjoint `w`, `y (w z w) = 0` iff `y w z = 0` — and the latter is
symmetric in `y` and `z`, being `(z w y)^*`. -/
private theorem su_ad_triple_zero {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {w y z : A} (hw : star w = w) (hy : IsStarProjection y)
    (hz : IsStarProjection z) : y * (w * z * w) = 0 ↔ y * w * z = 0 := by
  have e : star (z * w * y) = y * w * z := by
    rw [star_mul, star_mul, hw, hy.isSelfAdjoint.star_eq,
      hz.isSelfAdjoint.star_eq, mul_assoc]
  constructor
  · intro h
    have hstar : star (z * w * y) * (z * w * y) = 0 := by
      rw [e]
      calc y * w * z * (z * w * y) = y * (w * (z * z) * w) * y := by noncomm_ring
        _ = y * (w * z * w) * y := by rw [hz.isIdempotentElem.eq]
        _ = 0 := by rw [h, zero_mul]
    have hzy : z * w * y = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hstar
    rw [← e, hzy, star_zero]
  · intro h
    calc y * (w * z * w) = y * w * z * w := by noncomm_ring
      _ = 0 := by rw [h, zero_mul]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- Transport of a corner along an equality of the two projections: the
`Fact` instances that carry the algebra structure of `pAp` are `Prop`s, so
`subst` crosses them.  (This is what makes `su_stand_corner_ceil` below
possible: **169IV** produces a corner into `⌊a⌋A⌊a⌋`, and we need one into
`⌈a⌉A⌈a⌉` — the same algebra, but only after `⌊⌈a⌉⌋ = ⌈a⌉`.) -/
private theorem su_corner_transport {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (z z' : A) (hzz : z = z')
    [Fact (IsStarProjection z)] [Fact (IsStarProjection z')] (e : A)
    (h : Theses.NCPMap A (Theses.B.Dils.cornerSet A z))
    (hval : ∀ b : A, (h b).1 = z * b * z)
    (hc : Theses.B.Dils.IsCornerFor h e) :
    ∃ h' : Theses.NCPMap A (Theses.B.Dils.cornerSet A z'),
      (∀ b : A, (h' b).1 = z' * b * z') ∧ Theses.B.Dils.IsCornerFor h' e := by
  subst hzz
  exact ⟨h, hval, hc⟩

/-- **169IV at a ceiling**: `b ↦ ⌈a⌉b⌈a⌉ : A → ⌈a⌉A⌈a⌉` is a corner for the
projection `⌈a⌉`.  (The standard corner of **169IV** lands in `⌊·⌋A⌊·⌋`, and
`⌊⌈a⌉⌋ = ⌈a⌉`; the algebra is the *filter's* domain, which is why the
transport is needed at all.) -/
private theorem su_stand_corner_ceil {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] {a : A}
    (ha : 0 ≤ a) :
    ∃ h : Theses.NCPMap A (Theses.B.Dils.cornerSet A (Theses.A.VN.ceil a)),
      (∀ b : A, (h b).1
        = Theses.A.VN.ceil a * b * Theses.A.VN.ceil a) ∧
      Theses.B.Dils.IsCornerFor h (Theses.A.VN.ceil a) := by
  have hcp : IsStarProjection (Theses.A.VN.ceil a) := (Theses.A.VN.ceil_spec ha).1
  have hfz : Theses.A.VN.floor (Theses.A.VN.ceil a) = Theses.A.VN.ceil a :=
    su_floor_of_isStarProjection hcp
  obtain ⟨h, hval, hc⟩ := Theses.B.Dils.standard_corner_dils
    (Theses.A.VN.ceil a) ⟨hcp.nonneg, hcp.le_one⟩
  exact su_corner_transport _ _ hfz _ h hval hc

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- `√a ⌈a⌉ = √a` and `⌈a⌉ √a = √a` (`ceil_spec` through
`sqrt_mul_eq_zero_iff`); this is what makes `ad_{√a}` the standard filter
after the standard corner at `⌈a⌉`. -/
private theorem su_sqrt_mul_ceil {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] {a : A} (ha : 0 ≤ a) :
    CFC.sqrt a * Theses.A.VN.ceil a = CFC.sqrt a ∧
      Theses.A.VN.ceil a * CFC.sqrt a = CFC.sqrt a := by
  have hcp : IsStarProjection (Theses.A.VN.ceil a) := (Theses.A.VN.ceil_spec ha).1
  have hz : CFC.sqrt a * (1 - Theses.A.VN.ceil a) = 0 := by
    refine (Theses.A.VN.sqrt_mul_eq_zero_iff ha _).mpr ?_
    rw [mul_sub, mul_one, (Theses.A.VN.ceil_spec ha).2.1, sub_self]
  have h1 : CFC.sqrt a * Theses.A.VN.ceil a = CFC.sqrt a := by
    rw [mul_sub, mul_one, sub_eq_zero] at hz
    exact hz.symm
  refine ⟨h1, ?_⟩
  have h2 := congrArg star h1
  rwa [star_mul, hcp.isSelfAdjoint.star_eq,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq] at h2

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- Transport of a **filter** along an equality of the two projections, the
companion of `su_corner_transport` above and needed for the same reason: the
`Fact` instances that carry the algebra structure of `pAp` are `Prop`s, so
`subst` crosses them. -/
private theorem su_filter_transport {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (z z' : A) (hzz : z = z')
    [Fact (IsStarProjection z)] [Fact (IsStarProjection z')] (e w : A)
    (c : Theses.NCPMap (Theses.B.Dils.cornerSet A z) A)
    (hval : ∀ y : Theses.B.Dils.cornerSet A z, (c y : A) = w * y.1 * w)
    (hf : Theses.B.Dils.IsFilterFor c e) :
    ∃ c' : Theses.NCPMap (Theses.B.Dils.cornerSet A z') A,
      (∀ y : Theses.B.Dils.cornerSet A z', (c' y : A) = w * y.1 * w) ∧
      Theses.B.Dils.IsFilterFor c' e := by
  subst hzz
  exact ⟨c, hval, hf⟩

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- **169X at a ceiling**: the *inclusion* `⌈a⌉𝒜⌈a⌉ → 𝒜` is the standard
filter for the projection `⌈a⌉`, because `√⌈a⌉ = ⌈a⌉` and `⌈a⌉y⌈a⌉ = y` on
the corner.  (As with `su_stand_corner_ceil`, **169X** produces a filter on
`cornerSet A ⌈⌈a⌉⌉` and `⌈⌈a⌉⌉ = ⌈a⌉`, whence the transport.) -/
private theorem su_incl_of_ceil {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] {a : A} (ha : 0 ≤ a) :
    ∃ c : Theses.NCPMap
        (Theses.B.Dils.cornerSet A (Theses.A.VN.ceil a)) A,
      (∀ y : Theses.B.Dils.cornerSet A (Theses.A.VN.ceil a), (c y : A) = y.1) ∧
      Theses.B.Dils.IsFilterFor c (Theses.A.VN.ceil a) := by
  have hcp : IsStarProjection (Theses.A.VN.ceil a) := (Theses.A.VN.ceil_spec ha).1
  have hcc : Theses.A.VN.ceil (Theses.A.VN.ceil a) = Theses.A.VN.ceil a :=
    Theses.A.VN.ceil_of_isStarProjection hcp
  obtain ⟨c, hval, hfil⟩ :=
    Theses.B.Dils.dils_stand_filter (Theses.A.VN.ceil a) hcp.nonneg
  have hsq : CFC.sqrt (Theses.A.VN.ceil a) = Theses.A.VN.ceil a :=
    CFC.sqrt_unique hcp.isIdempotentElem.eq hcp.nonneg
  obtain ⟨c', hval', hfil'⟩ := su_filter_transport _ _ hcc _ _ c hval hfil
  refine ⟨c', fun y => ?_, hfil'⟩
  rw [hval' y, hsq]
  exact y.2


section DiaVN2

variable [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- `ad_w : b ↦ w b w` as a morphism `X ⟶ X` of `vN_cpsuᵒᵖ`, for `0 ≤ w`
with `w² ≤ 1` (complete positivity is **34V**.1 `ad_cp_1`, normality
**44VIII** `ad_normal`). -/
theorem su_exists_ad {X : WStarCPSU.{u}ᵒᵖ} {w : X.unop.base.carrier}
    (hw : 0 ≤ w) (hw1 : w * w ≤ 1) :
    ∃ k : X ⟶ X, ∀ x, k.unop.toNCPMap x = w * x * w := by
  have hsa : star w = w := (IsSelfAdjoint.of_nonneg hw).star_eq
  obtain ⟨m, hm⟩ : ∃ m : Theses.NCPSUMap X.unop.base.carrier X.unop.base.carrier,
      ∀ x, m.toNCPMap x = w * x * w := by
    refine ⟨mkNCPSU { toFun := fun x => star w * x * w
                      map_add' := fun x y => by noncomm_ring
                      map_smul' := fun c x => by simp } ?_ ?_ ?_,
      fun x => by show star w * x * w = w * x * w; rw [hsa]⟩
    · intro n c b
      have h := ad_cp_1 w n c b
      simpa [mul_assoc] using h
    · intro Dset s' hne hdir hlub
      have hb : BddAbove Dset := ⟨s', hlub.1⟩
      have hsd : Theses.dirSup Dset ⟨hne, hdir, hb⟩ = s' :=
        (Theses.isLUB_dirSup Dset ⟨hne, hdir, hb⟩).unique hlub
      have h := Theses.A.VN.ad_normal w Dset ⟨hne, hdir, hb⟩
      rw [hsd] at h
      exact h
    · show star w * 1 * w ≤ 1
      rw [hsa, mul_one]
      exact hw1
  exact ⟨Quiver.Hom.op m, hm⟩

/-- **206II at `vNᵒᵖ`**: `ad_w` is ⋄-self-adjoint for every `w ≥ 0`.  By
`su_diamondSelfAdjoint_of_symm` this is the symmetry of `ad_w^⋄`, which
`su_diaPull_val` turns into `y w z = 0 ⟺ z w y = 0`. -/
theorem su_diamondSelfAdjoint_ad {X : WStarCPSU.{u}ᵒᵖ} (g : X ⟶ X)
    {w : X.unop.base.carrier} (hw : 0 ≤ w)
    (hgw : ∀ x, g.unop.toNCPMap x = w * x * w) : DiamondSelfAdjoint g := by
  have hsa : star w = w := (IsSelfAdjoint.of_nonneg hw).star_eq
  have key : ∀ ps pt : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ), IsSharp ps → IsSharp pt →
      (ceilPred (g ≫ ps) ≼ EffectAlgebra.orth pt ↔
        suPredVal pt * w * suPredVal ps = 0) := by
    intro ps pt hps hpt
    have hz : IsStarProjection (suPredVal ps) := (su_isSharp_iff ps).mp hps
    have hy : IsStarProjection (suPredVal pt) := (su_isSharp_iff pt).mp hpt
    have hnn : (0 : X.unop.base.carrier) ≤ w * suPredVal ps * w := by
      have h := ncpsu_nonneg g.unop hz.nonneg
      rwa [hgw] at h
    have hceil : Theses.A.VN.ceil (w * suPredVal ps * w) ≤ 1 - suPredVal pt ↔
        (1 - suPredVal pt) * (w * suPredVal ps * w) = w * suPredVal ps * w :=
      (Theses.A.VN.ceil_basic_1 (w * suPredVal ps * w) (1 - suPredVal pt) hnn
        hy.one_sub).out 2 0
    refine Iff.trans (su_pred_le_iff (ceilPred (g ≫ ps)) (EffectAlgebra.orth pt)) ?_
    rw [su_ceilPred_val, suPredVal_comp, hgw,
      show suPredVal (EffectAlgebra.orth pt) = 1 - suPredVal pt from
        suPredVal_orth pt, hceil, sub_mul, one_mul, sub_eq_self]
    exact su_ad_triple_zero hsa hy hz
  have hstar : ∀ x y : X.unop.base.carrier, IsStarProjection x →
      IsStarProjection y → x * w * y = 0 → y * w * x = 0 := by
    intro x y hx hy0 h
    have h2 := congrArg star h
    rwa [star_mul, star_mul, hsa, hx.isSelfAdjoint.star_eq,
      hy0.isSelfAdjoint.star_eq, star_zero, ← mul_assoc] at h2
  refine su_diamondSelfAdjoint_of_symm g fun s t => ?_
  have hz : IsStarProjection (suPredVal s.1) := (su_isSharp_iff s.1).mp s.2
  have hy : IsStarProjection (suPredVal t.1) := (su_isSharp_iff t.1).mp t.2
  exact Iff.trans (key s.1 t.1 s.2 t.2)
    (Iff.trans ⟨fun h => hstar _ _ hy hz h, fun h => hstar _ _ hz hy h⟩
      (key t.1 s.1 t.2 s.2).symm)

end DiaVN2

/-- **201II at `vNᵒᵖ`** (eff.tex:4031 is the *Definition* of a pure map, a
comprehension after a quotient; what follows is supplied mathematics at
`vNᵒᵖ`, not a transcription of the point): `ad_{√a} : b ↦ √a b √a` is
**pure** — it is the standard filter `c_a` (a quotient,
`su_isQuotient_of_isFilterFor`) after the
standard corner at `⌈a⌉` (a *unital* corner, hence a comprehension,
`su_isComprehension_of_isCornerFor`), the composite being `ad_{√a}` because
`√a ⌈a⌉ = √a`. -/
theorem su_isPure_ad_sqrt {X : WStarCPSU.{u}ᵒᵖ} (g : X ⟶ X)
    {a : X.unop.base.carrier} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hga : ∀ x, g.unop.toNCPMap x = CFC.sqrt a * x * CFC.sqrt a) : IsPure g := by
  have hceilp : IsStarProjection (Theses.A.VN.ceil a) := (Theses.A.VN.ceil_spec ha0).1
  letI : Theses.VonNeumannAlgebra (Theses.B.Dils.cornerSet X.unop.base.carrier
      (Theses.A.VN.ceil a)) := Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
  obtain ⟨c, hcval, hcfil⟩ :=
    Theses.B.Dils.dils_stand_filter (B := X.unop.base.carrier) a ha0
  obtain ⟨hcor, hcorval, hcorfor⟩ :=
    su_stand_corner_ceil (A := X.unop.base.carrier) ha0
  have hcoru : hcor (1 : X.unop.base.carrier) = 1 := by
    refine Theses.B.Dils.cornerSet.val_injective ?_
    rw [hcorval, mul_one, hceilp.isIdempotentElem.eq,
      Theses.B.Dils.cornerSet.val_one]
  obtain ⟨ξ, hξ⟩ : ∃ ξ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of
        (Theses.B.Dils.cornerSet X.unop.base.carrier (Theses.A.VN.ceil a)))),
      ξ.unop.toNCPMap = c :=
    ⟨Quiver.Hom.op ⟨c, le_trans hcfil.2.1 ha1⟩, rfl⟩
  obtain ⟨π, hπ⟩ : ∃ π : Opposite.op (WStarCPSU.of (WStar.of
        (Theses.B.Dils.cornerSet X.unop.base.carrier (Theses.A.VN.ceil a)))) ⟶ X,
      π.unop.toNCPMap = hcor :=
    ⟨Quiver.Hom.op ⟨hcor, le_of_eq hcoru⟩, rfl⟩
  obtain ⟨p, hp⟩ := su_pred_exists (X := X) (a := 1 - a)
    (sub_nonneg.mpr ha1) (sub_le_self 1 ha0)
  obtain ⟨q, hq⟩ := su_pred_exists (X := X) hceilp.nonneg hceilp.le_one
  refine ⟨_, ξ, π, p, q, su_isQuotient_of_isFilterFor p ξ ?_,
    su_isComprehension_of_isCornerFor q π ?_ ?_, ?_⟩
  · rw [hξ, show suPredVal (EffectusPartialForm.orth p) = a by
      rw [suPredVal_orth, hp, sub_sub_cancel]]
    exact hcfil
  · rw [hπ]; exact hcoru
  · rw [hπ, hq]; exact hcorfor
  · -- `rw` cannot cross `cornerSet A ⌈a⌉` and
    -- `(Opposite.unop (Opposite.op (WStarCPSU.of (WStar.of (cornerSet A ⌈a⌉))))).base.carrier`,
    -- so the computation is a term-mode `Eq.trans` chain
    refine suop_hom_ext fun x => ?_
    obtain ⟨h1, h2⟩ := su_sqrt_mul_ceil (A := X.unop.base.carrier) ha0
    have e1 : ξ.unop.toNCPMap (π.unop.toNCPMap x) = c (hcor x) :=
      Eq.trans (congrArg (fun m => m (π.unop.toNCPMap x)) hξ)
        (congrArg (fun y => c y) (congrArg (fun m => m x) hπ))
    have e2 : ξ.unop.toNCPMap (π.unop.toNCPMap x)
        = CFC.sqrt a * (Theses.A.VN.ceil a * x * Theses.A.VN.ceil a)
          * CFC.sqrt a :=
      Eq.trans e1 (Eq.trans (hcval (hcor x))
        (congrArg (fun y => CFC.sqrt a * y * CFC.sqrt a) (hcorval x)))
    have hcalc : CFC.sqrt a * x * CFC.sqrt a
        = CFC.sqrt a * (Theses.A.VN.ceil a * x * Theses.A.VN.ceil a)
          * CFC.sqrt a :=
      calc CFC.sqrt a * x * CFC.sqrt a
          = CFC.sqrt a * Theses.A.VN.ceil a * x
              * (Theses.A.VN.ceil a * CFC.sqrt a) := by rw [h1, h2]
        _ = CFC.sqrt a * (Theses.A.VN.ceil a * x * Theses.A.VN.ceil a)
              * CFC.sqrt a := by noncomm_ring
    exact Eq.trans (hga x)
      (Eq.trans (Eq.trans hcalc e2.symm) (suop_comp_apply ξ π x).symm)

section AsrtVN

variable [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **211II at `vNᵒᵖ`**, the *existence* half of `existsUnique_asrt`, proved
without any &-effectus hypothesis: `ad_{√a}` is ⋄-positive and takes the
value `a` at the truth predicate.  (`su_isPure_ad_sqrt` gives purity, and
`ad_{√a} = ad_{⁴√a} ∘ ad_{⁴√a}` with `su_diamondSelfAdjoint_ad` gives the
square.)  What is left of **211IV** `vn_is_andthen_eff` is therefore
*uniqueness* alone; that is `su_asrt_unique_of_pure_sqrt`, which reaches
**105V** `positive-map-uniqueness` in `A/Proc` under the hypothesis of
**QUESTIONS B15**. -/
theorem su_exists_asrt {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃ k : X ⟶ X, DiamondPositive k ∧ k ≫ truth X = p ∧
      ∀ x, k.unop.toNCPMap x
        = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p) := by
  have ha0 : (0 : X.unop.base.carrier) ≤ suPredVal p := suPredVal_nonneg p
  have ha1 : suPredVal p ≤ 1 := suPredVal_le_one p
  have hs0 : (0 : X.unop.base.carrier) ≤ CFC.sqrt (suPredVal p) :=
    CFC.sqrt_nonneg _
  have hss : CFC.sqrt (suPredVal p) * CFC.sqrt (suPredVal p) = suPredVal p :=
    CFC.sqrt_mul_sqrt_self _ ha0
  have hs1 : CFC.sqrt (suPredVal p) ≤ 1 :=
    (Theses.A.VN.sqrt_mem_effects ⟨ha0, ha1⟩).2
  obtain ⟨k, hk⟩ := su_exists_ad (X := X) hs0 (by rw [hss]; exact ha1)
  obtain ⟨k2, hk2⟩ := su_exists_ad (X := X)
    (CFC.sqrt_nonneg (CFC.sqrt (suPredVal p)))
    (by rw [CFC.sqrt_mul_sqrt_self _ hs0]; exact hs1)
  refine ⟨k, ⟨su_isPure_ad_sqrt k ha0 ha1 hk, k2,
    su_diamondSelfAdjoint_ad k2 (CFC.sqrt_nonneg _) hk2, ?_⟩, ?_, hk⟩
  · refine suop_hom_ext fun y => ?_
    rw [hk, suop_comp_apply, hk2, hk2]
    calc CFC.sqrt (suPredVal p) * y * CFC.sqrt (suPredVal p)
        = CFC.sqrt (CFC.sqrt (suPredVal p)) * CFC.sqrt (CFC.sqrt (suPredVal p))
            * y * (CFC.sqrt (CFC.sqrt (suPredVal p))
              * CFC.sqrt (CFC.sqrt (suPredVal p))) := by
          rw [CFC.sqrt_mul_sqrt_self _ hs0]
      _ = CFC.sqrt (CFC.sqrt (suPredVal p))
            * (CFC.sqrt (CFC.sqrt (suPredVal p)) * y
              * CFC.sqrt (CFC.sqrt (suPredVal p)))
            * CFC.sqrt (CFC.sqrt (suPredVal p)) := by noncomm_ring
  · refine su_pred_ext ?_
    rw [suPredVal_comp, suPredVal_truth, hk, mul_one, hss]

end AsrtVN

/-! ### The `A/Proc` dictionary for purity (95I, 96I, 100I)

`su_isQuotient_of_isFilterFor` and `su_isComprehension_of_isCornerFor` above
read the **`B/Dils`** universal properties (dils.tex 169VIII, 169II) inside
`vN_cpsuᵒᵖ`.  **211IV** needs the same dictionary against the **`A/Proc`**
notions — proc.tex **96I** `IsFilter`, **95I** `IsCornerOf`/`IsCornerMap`
and **100I** `IsPure` — because 105V `positive-map-uniqueness` and 100III
`pure-fundamental` are stated with those; and it needs it in *both*
directions.  The mismatches, and why each is harmless:

* `A/Proc`'s universal properties quantify over ncp-maps where the effectus
  quantifies over its morphisms (ncp**su**-maps).  Every mediating map that
  occurs is subunital anyway: for a filter `c` because `c(g(1)) = f(1) ≤
  c(1)` and filters are **bipositive** (98II.3 `filter_basic_3`); for a
  corner because the corner is unital (comprehensions are total, 202VIII).
* `A/Proc`'s corner condition is `f(p^⊥) = 0` where the effectus asks
  `p ∘ f = 1 ∘ f`; for a *linear* map those are the same equation.
* an `A/Proc` filter is a filter *for* `c(1)`; an effectus quotient is one
  *for* `p`, with `1 ∘ ξ ≼ pᵖ` — the two agree at `c(1) = pᵖ`.
* the effectus quantifies over its own objects, which are exactly the von
  Neumann algebras of `A/Proc`. -/

section ProcPurity

variable [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **197IV at `vNᵒᵖ`** against `A/Proc`: a map whose ncpsu-map is a
**filter** (proc.tex 96I) taking the value `pᵖ` at `1` is a quotient for
`p`. -/
theorem su_isQuotient_of_isFilter {X Q : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (ξ : X ⟶ Q)
    (hfil : Theses.A.Proc.IsFilter ξ.unop.toNCPMap)
    (hval : ξ.unop.toNCPMap (1 : Q.unop.base.carrier)
      = suPredVal (EffectusPartialForm.orth p)) :
    IsQuotient p ξ := by
  constructor
  · refine (su_pred_le_iff _ _).mpr ?_
    show suPredVal (ξ ≫ truth Q) ≤ suPredVal (EffectusPartialForm.orth p)
    rw [suPredVal_comp, suPredVal_truth, hval]
  · intro Y f hf
    have hf1 : f.unop.toNCPMap (1 : Y.unop.base.carrier)
        ≤ ξ.unop.toNCPMap (1 : Q.unop.base.carrier) := by
      have h1 := (su_pred_le_iff (f ≫ truth Y) (EffectusPartialForm.orth p)).mp hf
      rw [suPredVal_comp, suPredVal_truth] at h1
      rw [hval]
      exact h1
    obtain ⟨g, hg, huniq⟩ :=
      hfil.universal Y.unop.base.carrier f.unop.toNCPMap hf1
    have hsub : g (1 : Y.unop.base.carrier) ≤ (1 : Q.unop.base.carrier) := by
      have hlin : ξ.unop.toNCPMap ((1 : Q.unop.base.carrier) - g 1)
          = ξ.unop.toNCPMap 1 - ξ.unop.toNCPMap (g 1) :=
        map_sub (ncpLin ξ.unop.toNCPMap) _ _
      have h0 : (0 : X.unop.base.carrier)
          ≤ ξ.unop.toNCPMap ((1 : Q.unop.base.carrier) - g 1) := by
        rw [hlin, ← hg 1]
        exact sub_nonneg.mpr hf1
      exact sub_nonneg.mp ((Theses.A.Proc.filter_basic_3 _ hfil _).mp h0)
    obtain ⟨k, hk⟩ : ∃ k : Q ⟶ Y, ∀ y, k.unop.toNCPMap y = g y :=
      ⟨Quiver.Hom.op ⟨g, hsub⟩, fun _ => rfl⟩
    refine ⟨k, suop_hom_ext fun y => ?_, fun k' hk' => ?_⟩
    · rw [suop_comp_apply, hk]
      exact (hg y).symm
    · have hk'' : ∀ y, f.unop.toNCPMap y = ξ.unop.toNCPMap (k'.unop.toNCPMap y) :=
        fun y => (suop_congr hk' y).symm.trans (suop_comp_apply ξ k' y)
      refine suop_hom_ext fun y => ?_
      rw [hk]
      exact congrArg
        (fun m : Theses.NCPMap Y.unop.base.carrier Q.unop.base.carrier => m y)
        (huniq k'.unop.toNCPMap hk'')

/-- **199V at `vNᵒᵖ`** against `A/Proc`: a map whose ncpsu-map is a
**unital corner** of the effect named by `q` (proc.tex 95I) is a
comprehension for `q`.  Unitality is 95I's own convention, not an extra
hypothesis (proc.tex:280); the Example's biconditional is
`su_isComprehension_iff_isCornerMap` below. -/
theorem su_isComprehension_of_isCornerOf {W X : WStarCPSU.{u}ᵒᵖ}
    (q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (π : W ⟶ X)
    (hu : π.unop.toNCPMap (1 : X.unop.base.carrier) = (1 : W.unop.base.carrier))
    (hc : Theses.A.Proc.IsCornerOf (suPredVal q) π.unop.toNCPMap) :
    IsComprehension q π := by
  constructor
  · refine su_pred_ext ?_
    rw [suPredVal_comp, suPredVal_comp, suPredVal_truth]
    have h := hc.map_perp
    have hlin : π.unop.toNCPMap ((1 : X.unop.base.carrier) - suPredVal q)
        = π.unop.toNCPMap 1 - π.unop.toNCPMap (suPredVal q) :=
      map_sub (ncpLin π.unop.toNCPMap) _ _
    rw [hlin] at h
    exact (sub_eq_zero.mp h).symm
  · intro Z g hgq
    have hg0 : g.unop.toNCPMap ((1 : X.unop.base.carrier) - suPredVal q) = 0 := by
      have h1 := congrArg suPredVal hgq
      rw [suPredVal_comp, suPredVal_comp, suPredVal_truth] at h1
      have hlin : g.unop.toNCPMap ((1 : X.unop.base.carrier) - suPredVal q)
          = g.unop.toNCPMap 1 - g.unop.toNCPMap (suPredVal q) :=
        map_sub (ncpLin g.unop.toNCPMap) _ _
      rw [hlin, h1, sub_self]
    obtain ⟨g', hg', huniq⟩ :=
      hc.universal Z.unop.base.carrier g.unop.toNCPMap hg0
    have hsub : g' (1 : W.unop.base.carrier) ≤ 1 := by
      have h := hg' (1 : X.unop.base.carrier)
      rw [hu] at h
      rw [← h]
      exact g.unop.subunital'
    obtain ⟨k, hk⟩ : ∃ k : Z ⟶ W, ∀ x, k.unop.toNCPMap x = g' x :=
      ⟨Quiver.Hom.op ⟨g', hsub⟩, fun _ => rfl⟩
    refine ⟨k, suop_hom_ext fun x => ?_, fun k' hk' => ?_⟩
    · rw [suop_comp_apply, hk]
      exact (hg' x).symm
    · have hk'' : ∀ x, g.unop.toNCPMap x = k'.unop.toNCPMap (π.unop.toNCPMap x) :=
        fun x => (suop_congr hk' x).symm.trans (suop_comp_apply k' π x)
      refine suop_hom_ext fun x => ?_
      rw [hk]
      exact congrArg
        (fun m : Theses.NCPMap W.unop.base.carrier Z.unop.base.carrier => m x)
        (huniq k'.unop.toNCPMap hk'')

/-- **197IV at `vNᵒᵖ`**, the converse: the ncpsu-map of a **quotient** is a
filter in the sense of proc.tex 96I.  Any two quotients for `p` differ by an
isomorphism (197V.2), the standard filter `c_{pᵖ}` (proc.tex 98I) gives one,
and isomorphisms are filters (`isFilter_of_iso`) which compose with filters
(98III). -/
theorem su_isFilter_of_isQuotient {X Q : WStarCPSU.{u}ᵒᵖ}
    {p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} {ξ : X ⟶ Q} (hξ : IsQuotient p ξ) :
    Theses.A.Proc.IsFilter ξ.unop.toNCPMap := by
  set b : X.unop.base.carrier := suPredVal (EffectusPartialForm.orth p) with hb
  have hb0 : (0 : X.unop.base.carrier) ≤ b := suPredVal_nonneg _
  have hb1 : b ≤ 1 := suPredVal_le_one _
  have hsub : (Theses.A.Proc.stdFilter b)
      (1 : Theses.A.Proc.Corner X.unop.base.carrier (Theses.A.VN.ceil b)) ≤ 1 := by
    rw [Theses.A.Proc.stdFilter_one hb0]; exact hb1
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of
        (Theses.A.Proc.Corner X.unop.base.carrier (Theses.A.VN.ceil b)))),
      ξ₀.unop.toNCPMap = Theses.A.Proc.stdFilter b :=
    ⟨Quiver.Hom.op ⟨Theses.A.Proc.stdFilter b, hsub⟩, rfl⟩
  have hfil₀ : Theses.A.Proc.IsFilter ξ₀.unop.toNCPMap := by
    rw [hξ₀]; exact Theses.A.Proc.isFilter_stdFilter b hb0
  have hq₀ : IsQuotient p ξ₀ := by
    refine su_isQuotient_of_isFilter p ξ₀ hfil₀ ?_
    rw [hξ₀]; exact Theses.A.Proc.stdFilter_one hb0
  obtain ⟨θ, hθiso, hθ, -⟩ := quotient_basics_2 hξ hq₀
  haveI := hθiso
  have hcomp : ξ.unop.toNCPMap
      = Theses.A.Proc.ncpComp ξ₀.unop.toNCPMap θ.unop.toNCPMap := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [Theses.A.Proc.ncpComp_apply]
    exact (suop_congr hθ y).symm.trans (suop_comp_apply ξ₀ θ y)
  have hgf : ∀ a : Q.unop.base.carrier,
      (inv θ).unop.toNCPMap (θ.unop.toNCPMap a) = a := by
    intro a
    have h := suop_congr (IsIso.inv_hom_id θ) a
    rw [suop_comp_apply] at h
    exact h.trans (su_id_apply _)
  have hfg : ∀ y, θ.unop.toNCPMap ((inv θ).unop.toNCPMap y) = y := by
    intro y
    have h := suop_congr (IsIso.hom_inv_id θ) y
    rw [suop_comp_apply] at h
    exact h.trans (su_id_apply _)
  rw [hcomp]
  exact Theses.A.Proc.filters_composition θ.unop.toNCPMap ξ₀.unop.toNCPMap
    (Theses.A.Proc.isFilter_of_iso θ.unop.toNCPMap (inv θ).unop.toNCPMap hgf hfg)
    hfil₀

/-- **199V at `vNᵒᵖ`**, the converse: the ncpsu-map of a **comprehension**
is a unital corner in the sense of proc.tex 95I.  Comprehensions for `q`
differ by an isomorphism (199VII.2), the standard corner `π_q` (proc.tex
98I) gives one, comprehensions are total (202VIII), and corners compose
(98VI). -/
theorem su_isCornerMap_of_isComprehension {W X : WStarCPSU.{u}ᵒᵖ}
    {q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} {π : W ⟶ X} (hπ : IsComprehension q π) :
    Theses.A.Proc.IsCornerMap π.unop.toNCPMap := by
  set a : X.unop.base.carrier := suPredVal q with ha
  have ha0 : (0 : X.unop.base.carrier) ≤ a := suPredVal_nonneg _
  have ha1 : a ≤ 1 := suPredVal_le_one _
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : Opposite.op (WStarCPSU.of (WStar.of
        (Theses.A.Proc.Corner X.unop.base.carrier (Theses.A.VN.floor a)))) ⟶ X,
      π₀.unop.toNCPMap = (Theses.A.Proc.stdCorner a).toNCPMap :=
    ⟨Quiver.Hom.op ⟨(Theses.A.Proc.stdCorner a).toNCPMap,
      le_of_eq (Theses.A.Proc.stdCorner a).unital'⟩, rfl⟩
  have hcorner₀ : Theses.A.Proc.IsCornerMap (Theses.A.Proc.stdCorner a).toNCPMap :=
    ⟨(Theses.A.Proc.stdCorner a).unital', a, ⟨ha0, ha1⟩,
      Theses.A.Proc.isCornerOf_stdCorner a ⟨ha0, ha1⟩⟩
  have hcorner₀' : Theses.A.Proc.IsCornerMap π₀.unop.toNCPMap := by
    rw [hπ₀]; exact hcorner₀
  have hcompr₀ : IsComprehension q π₀ := by
    refine su_isComprehension_of_isCornerOf q π₀ ?_ ?_
    · rw [hπ₀]; exact (Theses.A.Proc.stdCorner a).unital'
    · rw [hπ₀]; exact Theses.A.Proc.isCornerOf_stdCorner a ⟨ha0, ha1⟩
  obtain ⟨θ, hθiso, hθ, -⟩ := compr_basics_2 hπ hcompr₀
  haveI := hθiso
  have hcomp : π.unop.toNCPMap
      = Theses.A.Proc.ncpComp θ.unop.toNCPMap π₀.unop.toNCPMap := by
    refine DFunLike.ext _ _ fun x => ?_
    rw [Theses.A.Proc.ncpComp_apply]
    exact (suop_congr hθ x).symm.trans (suop_comp_apply θ π₀ x)
  have hgf : ∀ y, (inv θ).unop.toNCPMap (θ.unop.toNCPMap y) = y := by
    intro y
    have h := suop_congr (IsIso.inv_hom_id θ) y
    rw [suop_comp_apply] at h
    exact h.trans (su_id_apply _)
  have hfg : ∀ y, θ.unop.toNCPMap ((inv θ).unop.toNCPMap y) = y := by
    intro y
    have h := suop_congr (IsIso.hom_inv_id θ) y
    rw [suop_comp_apply] at h
    exact h.trans (su_id_apply _)
  have hθu : θ.unop.toNCPMap 1 = 1 := (su_isTotal_iff θ).mp (iso_isTotal θ)
  rw [hcomp]
  exact Theses.A.Proc.corners_composition π₀.unop.toNCPMap
    θ.unop.toNCPMap hcorner₀'
    (Theses.A.Proc.isCornerMap_of_iso θ.unop.toNCPMap (inv θ).unop.toNCPMap
      hgf hfg hθu)

/-- **199V** (eff.tex:3933, unlabelled Examples), first sentence as
printed: *"In `\\op\\vN` comprehensions are exactly the same thing as
corners"* — the **biconditional**, which neither of the two implications
above states on its own.

"Corner" is proc.tex 95I's, and 95I fixes the convention (proc.tex:280) that
a corner is always a *unital* corner unless stated otherwise; `IsCornerMap`
is that notion (unital, and a corner of *some* effect).  So the two halves
compose without any hypothesis beyond the print: forward is
`su_isCornerMap_of_isComprehension`, backward is
`su_isComprehension_of_isCornerOf` fed the unitality `IsCornerMap` carries,
with the effect `p` of the corner named by a predicate through
`su_pred_exists`. -/
theorem su_isComprehension_iff_isCornerMap {W X : WStarCPSU.{u}ᵒᵖ} (π : W ⟶ X) :
    (∃ q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ), IsComprehension q π) ↔
      Theses.A.Proc.IsCornerMap π.unop.toNCPMap := by
  constructor
  · rintro ⟨q, hq⟩
    exact su_isCornerMap_of_isComprehension hq
  · rintro ⟨hu, p, hp, hcorner⟩
    obtain ⟨q, hq⟩ := su_pred_exists (X := X) (a := p) hp.1 hp.2
    exact ⟨q, su_isComprehension_of_isCornerOf q π hu (by rw [hq]; exact hcorner)⟩

/-- **201II at `vNᵒᵖ`**: a pure map of `vN_cpsuᵒᵖ` has a pure ncpsu-map
(proc.tex 100I).  201II is the Definition of purity in an effectus; this
bridge between it and proc.tex's is supplied, not transcribed. -/
theorem su_procPure_of_isPure {X Y : WStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hf : IsPure f) : Theses.A.Proc.IsPure f.unop.toNCPMap := by
  obtain ⟨Q, ξ, π, p, q, hξ, hπ, hfe⟩ := hf
  have hcomp : f.unop.toNCPMap
      = Theses.A.Proc.ncpComp ξ.unop.toNCPMap π.unop.toNCPMap := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [Theses.A.Proc.ncpComp_apply]
    exact (suop_congr hfe y).trans (suop_comp_apply ξ π y)
  rw [hcomp]
  exact Theses.A.Proc.IsPure.comp
    (Theses.A.Proc.IsPure.filter (su_isFilter_of_isQuotient hξ))
    (Theses.A.Proc.IsPure.corner (su_isCornerMap_of_isComprehension hπ))

/-- **100III at `vNᵒᵖ`**, the converse: a map of `vN_cpsuᵒᵖ` whose ncpsu-map
is pure (proc.tex 100I) is pure in the effectus.  `pure-fundamental` writes
it as a filter after a *unital* corner, and the two dictionary lemmas above
turn those into a quotient and a comprehension. -/
theorem su_isPure_of_procPure {X Y : WStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hf : Theses.A.Proc.IsPure f.unop.toNCPMap) : IsPure f := by
  obtain ⟨Z, _, _, _, _, π, c, hπ, hc, hfac⟩ :=
    ((Theses.A.Proc.pure_fundamental f.unop.toNCPMap).out 0 1).mp hf
  have hfx : ∀ y : Y.unop.base.carrier, f.unop.toNCPMap y = c (π y) := by
    intro y
    rw [hfac, Theses.A.Proc.ncpComp_apply]
  have hc1 : (c 1 : X.unop.base.carrier) = f.unop.toNCPMap 1 := by
    rw [hfx 1, hπ.1]
  have hc0 : (0 : X.unop.base.carrier) ≤ c 1 := by
    rw [hc1]; exact ncpsu_nonneg f.unop zero_le_one
  have hc1le : (c 1 : X.unop.base.carrier) ≤ 1 := by
    rw [hc1]; exact f.unop.subunital'
  obtain ⟨ξ, hξ⟩ : ∃ ξ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of Z)),
      ξ.unop.toNCPMap = c :=
    ⟨Quiver.Hom.op ⟨c, hc1le⟩, rfl⟩
  obtain ⟨π', hπ'⟩ : ∃ π' : Opposite.op (WStarCPSU.of (WStar.of Z)) ⟶ Y,
      π'.unop.toNCPMap = π :=
    ⟨Quiver.Hom.op ⟨π, le_of_eq hπ.1⟩, rfl⟩
  obtain ⟨p₀, hp₀⟩ := su_pred_exists (X := X) (a := 1 - c 1)
    (sub_nonneg.mpr hc1le) (sub_le_self 1 hc0)
  obtain ⟨r, hr, hcorner⟩ := hπ.2
  obtain ⟨q₀, hq₀⟩ := su_pred_exists (X := Y) (a := r) hr.1 hr.2
  refine ⟨_, ξ, π', p₀, q₀, ?_, ?_, ?_⟩
  · refine su_isQuotient_of_isFilter p₀ ξ ?_ ?_
    · rw [hξ]; exact hc
    · have hval : suPredVal (EffectusPartialForm.orth p₀)
          = (c 1 : X.unop.base.carrier) := by
        rw [suPredVal_orth, hp₀, sub_sub_cancel]
      exact (congrArg (fun m : Theses.NCPMap Z X.unop.base.carrier => m 1) hξ).trans
        hval.symm
  · refine su_isComprehension_of_isCornerOf q₀ π' ?_ ?_
    · rw [hπ']; exact hπ.1
    · rw [hπ', hq₀]; exact hcorner
  · refine suop_hom_ext fun y => ?_
    rw [suop_comp_apply, hξ, hπ']
    exact hfx y

/-- **211II.2 at `vNᵒᵖ`** (eff.tex:4808): a **quotient after a
comprehension is pure** — the second axiom of an &-effectus.  This is
`pure-fundamental` in `A/Proc` (eff.tex:4862 cites exactly that): the
ncpsu-map of `ξ ∘ π` is a *corner after a filter*, and 100I closes purity
under composition. -/
theorem su_quot_after_compr_pure {X Y Z : WStarCPSU.{u}ᵒᵖ}
    {p q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} (π : Z ⟶ X) (ξ : X ⟶ Y)
    (hπ : IsComprehension p π) (hξ : IsQuotient q ξ) : IsPure (π ≫ ξ) := by
  refine su_isPure_of_procPure ?_
  have hcomp : (π ≫ ξ).unop.toNCPMap
      = Theses.A.Proc.ncpComp π.unop.toNCPMap ξ.unop.toNCPMap := by
    refine DFunLike.ext _ _ fun z => ?_
    rw [Theses.A.Proc.ncpComp_apply]
    exact suop_comp_apply π ξ z
  rw [hcomp]
  exact Theses.A.Proc.IsPure.comp
    (Theses.A.Proc.IsPure.corner (su_isCornerMap_of_isComprehension hπ))
    (Theses.A.Proc.IsPure.filter (su_isFilter_of_isQuotient hξ))

/-! ### **201III**, second sentence: the pure maps `B(ℋ) → B(𝒦)`

eff.tex:4038 goes on: *"The pure maps `B(ℋ) → B(𝒦)` are exactly the maps of
the form `ad_T` where `T` is a contractive map `𝒦 → ℋ`."*  dils.tex
**170II**.1 (`Theses.B.Dils.dils_examples_pure_1`) prints the same sentence
one category over — for ncp-maps, and for an arbitrary *bounded* `T` — and
the two printings agree rather than conflict: the morphisms of `vN_cpsuᵒᵖ`
are **subunital**, `ad_T(1) = T*T` has norm `‖T‖²`, and so `ad_T` is a
morphism of this category exactly when `T` is a contraction
(`su_conjOperator_subunital_iff`).

Three things have to be added to 170II.1: `B(ℋ)` as an object of the
effectus (`suBH`), the contractivity clause, and the bridge from
effectus-purity to the purity of `B/Dils`.  The first sentence of 201III
(`su_procPure_of_isPure`, `su_isPure_of_procPure`, above) carries
effectus-purity as far as `Theses.A.Proc.IsPure`; the remaining leg is
`Theses.B.Dils.isPureMap_of_procIsPure` and its converse
`su_procIsPure_of_isPureMap` below.  The merge of the two purity predicates
is `B/Dils`' `section ProcPure`; the `[VonNeumannAlgebra C]` residue it
leaves is not needed here once the factorisation is merely *assumed to
exist*. -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- **168IV ⟹ 170I at von Neumann objects, with no hypothesis on the
intermediate algebra**: a `Theses.B.Dils.IsPureMap` between von Neumann
algebras is pure in the inductive sense of **170I**,
`Theses.A.Proc.IsPure`.

`Theses.B.Dils.procIsPure_of_factorisation` proves this of a *given*
factorisation `φ = c ∘ h`, and needs `[VonNeumannAlgebra C]` on the algebra
in the middle — 170I's `comp` constructor demands it and `IsPureMap`, whose
intermediate algebra is a bare C\*-algebra, does not supply it.  The
hypothesis is dispensable once the factorisation is only *assumed to exist*:
a filter `c` for `b` and the standard filter `c_b : ⌈b⌉B⌈b⌉ → B` of **169X**
mediate each other, and filters are injective (**169XII**
`dils_filters_injective`), so the two mediating maps `w`, `w'` are mutually
inverse; `w' ∘ h` is then again a corner for the same effect
(`isCornerFor_of_ncpIso`), and `φ = c_b ∘ (w' ∘ h)` is a factorisation whose
middle is `⌈b⌉B⌈b⌉` — a von Neumann algebra.

With `Theses.B.Dils.isPureMap_of_procIsPure` this makes the two chapters'
notions of purity **equivalent** at von Neumann objects.  The statement is a
`B/Dils` one and belongs beside `procIsPure_of_factorisation`; it is here
because this file is the leaf in which 201III lives. -/
theorem su_procIsPure_of_isPureMap {A B : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [Theses.VonNeumannAlgebra A] [Theses.VonNeumannAlgebra B]
    {φ : Theses.NCPMap A B} (hφ : Theses.B.Dils.IsPureMap φ) :
    Theses.A.Proc.IsPure φ := by
  obtain ⟨C, _, _, _, h, c, hcorner, hfilter, hfac⟩ := hφ
  obtain ⟨b, hb⟩ := hfilter
  obtain ⟨a, hCF⟩ := hcorner
  obtain ⟨cst, -, hcst⟩ := Theses.B.Dils.dils_stand_filter b hb.1
  letI _vn := Theses.B.Dils.cornerSet_vonNeumannAlgebra B (Theses.A.VN.ceil b)
  obtain ⟨w, hw, -⟩ :=
    hb.2.2 _ inferInstance inferInstance inferInstance cst hcst.2.1
  obtain ⟨w', hw', -⟩ :=
    hcst.2.2 C inferInstance inferInstance inferInstance c hb.2.1
  have hcinj : Function.Injective ⇑c :=
    Theses.B.Dils.dils_filters_injective c ⟨b, hb⟩
  have hcstinj : Function.Injective ⇑cst :=
    Theses.B.Dils.dils_filters_injective cst ⟨b, hcst⟩
  have hww' : ∀ x : C, w.toNCPMap (w'.toNCPMap x) = x := fun x =>
    hcinj (by rw [hw (w'.toNCPMap x), hw' x])
  have hw'w : ∀ y, w'.toNCPMap (w.toNCPMap y) = y := fun y =>
    hcstinj (by rw [hw' (w.toNCPMap y), hw y])
  obtain ⟨π, hπ⟩ := Theses.A.Proc.exists_ncpComp w'.toNCPMap h
  have hcorner' : Theses.B.Dils.IsCornerFor π a :=
    Theses.B.Dils.isCornerFor_of_ncpIso hCF w.toNCPMap w'.toNCPMap
      (fun x => by rw [hπ, hww']) hw'w
  exact Theses.B.Dils.procIsPure_of_factorisation ⟨a, hcorner'⟩ ⟨b, hcst⟩
    fun x => by rw [hπ, hw', hfac]

section BofH

open scoped ComplexInnerProductSpace

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- `ad_T` is a positive map: **34V**.2 `ad_cp_2` says it is completely
positive, and **25II**.2 `astara_pos_basic_2_cp` that a completely positive
map is positive. -/
theorem su_conjOperator_nonneg (T : K →L[ℂ] H) {a : H →L[ℂ] H} (ha : 0 ≤ a) :
    0 ≤ conjOperator T a :=
  astara_pos_basic_2_cp (conjOperator T) (ad_cp_2 T) a ha

/-- `ad_T : B(ℋ) → B(𝒦)`, `a ↦ T*aT`, as a positive linear map. -/
noncomputable def suAdP (T : K →L[ℂ] H) : (H →L[ℂ] H) →ₚ[ℂ] (K →L[ℂ] K) where
  toLinearMap := conjOperator T
  monotone' := fun a a' h => by
    have h2 := su_conjOperator_nonneg T (sub_nonneg.mpr h)
    rw [map_sub] at h2
    exact sub_nonneg.mp h2

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
@[simp] theorem suAdP_apply (T : K →L[ℂ] H) (a : H →L[ℂ] H) :
    suAdP T a = conjOperator T a := rfl

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- `ad_T` is **normal**: by **48II** `normal_faithful` it is enough that
`ω ∘ ad_T` be normal for the vector functionals `ω`, which separate
(**42V**.2), and `⟪y, T*a(Ty)⟫ = ⟪Ty, a(Ty)⟫` is again one. -/
theorem suAdP_normal (T : K →L[ℂ] H) : Theses.PreservesDirSups ⇑(suAdP T) := by
  set Ω : Set (NPFunctional (K →L[ℂ] K)) :=
    {ν | ∃ y ∈ (Set.univ : Set K), ν = Theses.A.VN.vectorNP y} with hΩ
  have hfaith : Theses.A.VN.FaithfulCollection Ω :=
    Theses.A.VN.faithfulCollection_vectorNP Set.univ
      (fun R h => ContinuousLinearMap.ext fun y => h y (Set.mem_univ y))
  refine (Theses.A.VN.normal_faithful Ω hfaith (suAdP T)).mpr ?_
  rintro ν ⟨y, -, rfl⟩
  have hpt : ∀ a : H →L[ℂ] H, (Theses.A.VN.vectorNP y (suAdP T a) : ℂ)
      = Theses.A.VN.vectorNP (T y) a := by
    intro a
    have happ : (conjOperator T a) y
        = ContinuousLinearMap.adjoint T (a (T y)) := rfl
    rw [Theses.A.VN.vectorNP_apply, Theses.A.VN.vectorNP_apply, suAdP_apply, happ,
      ContinuousLinearMap.adjoint_inner_right]
  intro D s hne hdir hlub
  have h := (Theses.A.VN.vectorNP (T y)).preservesDirSups' D s hne hdir hlub
  simp only [hpt]
  exact h

/-- `ad_T : B(ℋ) → B(𝒦)` as an ncp-map. -/
noncomputable def suAdNCP (T : K →L[ℂ] H) :
    Theses.NCPMap (H →L[ℂ] H) (K →L[ℂ] K) where
  toCompletelyPositiveMap :=
    { toLinearMap := conjOperator T
      map_cstarMatrix_nonneg' := ((cp_iff (conjOperator T)).out 0 1).mp (ad_cp_2 T) }
  preservesDirSups' := suAdP_normal T

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
@[simp] theorem suAdNCP_apply (T : K →L[ℂ] H) (a : H →L[ℂ] H) :
    suAdNCP T a = conjOperator T a := rfl

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- `ad_T(1) = T*T`. -/
theorem su_conjOperator_one (T : K →L[ℂ] H) :
    conjOperator T (1 : H →L[ℂ] H) = ContinuousLinearMap.adjoint T ∘L T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp [conjOperator]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- **The contractivity clause of 201III**: `ad_T` is subunital — i.e. is a
morphism of `vN_cpsuᵒᵖ` — exactly when `T` is a contraction.  `ad_T(1) =
T*T` is positive with `‖T*T‖ = ‖T‖²`, and a positive element is `≤ 1` iff
its norm is (Mathlib's `CStarAlgebra.norm_le_one_iff_of_nonneg`). -/
theorem su_conjOperator_subunital_iff (T : K →L[ℂ] H) :
    conjOperator T (1 : H →L[ℂ] H) ≤ 1 ↔ ‖T‖ ≤ 1 := by
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _
      (su_conjOperator_nonneg T (zero_le_one (α := H →L[ℂ] H))),
    su_conjOperator_one, ContinuousLinearMap.norm_adjoint_comp_self]
  constructor
  · intro h; nlinarith [norm_nonneg T]
  · intro h; nlinarith [norm_nonneg T]

/-- `B(ℋ)` as an object of `vNᵒᵖ`. -/
noncomputable abbrev suBH (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : WStarCPSU.{u}ᵒᵖ :=
  Opposite.op (WStarCPSU.of (WStar.of (H →L[ℂ] H)))

/-- `ad_T`, for a contraction `T : 𝒦 → ℋ`, as a morphism
`B(ℋ) → B(𝒦)` of `vNᵒᵖ`. -/
noncomputable def suAdHom (T : K →L[ℂ] H) (hT : ‖T‖ ≤ 1) : suBH K ⟶ suBH H :=
  Quiver.Hom.op ⟨suAdNCP T, (su_conjOperator_subunital_iff T).mpr hT⟩

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)] in
@[simp] theorem suAdHom_apply (T : K →L[ℂ] H) (hT : ‖T‖ ≤ 1) (a : H →L[ℂ] H) :
    (suAdHom T hT).unop.toNCPMap a = conjOperator T a := rfl

/-- **201III** (eff.tex:4038, Example), **second sentence**: the pure maps
`B(ℋ) → B(𝒦)` of `vNᵒᵖ` are exactly the maps `ad_T`, `a ↦ T*aT`, for a
**contractive** `T : 𝒦 → ℋ`.

**⇒** the first sentence (`su_procPure_of_isPure`) makes the ncpsu-map of a
pure map pure in the sense of proc.tex **100I**, `isPureMap_of_procIsPure`
turns that into dils.tex's **168IV** normal form, and **170II**.1
`dils_examples_pure_1` produces the bounded `T`.  It is contractive because
`ad_T(1) = f(1) ≤ 1`, `f` being a morphism of `vN_cpsuᵒᵖ`.

**⇐** the same three steps backwards, the middle one being
`su_procIsPure_of_isPureMap`; the contractivity hypothesis is not used here,
since `f` is a morphism already.

`su_pure_bh_ad` is the other half of "exactly": every contraction does give
such a morphism, and it is pure. -/
theorem su_pure_bh_iff (f : suBH K ⟶ suBH H) :
    IsPure f ↔ ∃ T : K →L[ℂ] H, ‖T‖ ≤ 1 ∧
      ∀ a : H →L[ℂ] H, f.unop.toNCPMap a = conjOperator T a := by
  constructor
  · intro hf
    obtain ⟨T, hT⟩ := (Theses.B.Dils.dils_examples_pure_1 f.unop.toNCPMap).mp
      (Theses.B.Dils.isPureMap_of_procIsPure (su_procPure_of_isPure hf))
    refine ⟨T, ?_, hT⟩
    refine (su_conjOperator_subunital_iff T).mp ?_
    rw [← hT 1]
    exact f.unop.subunital'
  · rintro ⟨T, -, hT⟩
    exact su_isPure_of_procPure (su_procIsPure_of_isPureMap
      ((Theses.B.Dils.dils_examples_pure_1 f.unop.toNCPMap).mpr ⟨T, hT⟩))

/-- **201III**, second sentence, the "every `ad_T` occurs" half: for a
contraction `T : 𝒦 → ℋ` the morphism `ad_T : B(ℋ) → B(𝒦)` of `vNᵒᵖ` is
pure. -/
theorem su_pure_bh_ad (T : K →L[ℂ] H) (hT : ‖T‖ ≤ 1) : IsPure (suAdHom T hT) :=
  (su_pure_bh_iff (suAdHom T hT)).mpr ⟨T, hT, fun _ => rfl⟩

end BofH

/-! ### The ⋄-layer of 211II, and where eff.tex and proc.tex part company

`su_exists_asrt` above settles the *existence* half of 211II.1.  For
*uniqueness* eff.tex:4861 cites **105V** `positive-map-uniqueness`, and that
citation does not quite land, for a reason that is a difference between the
two theses' definitions and not an artefact of this rendering:

* proc.tex **103I** calls `f` **⋄-self-adjoint** when it is *pure* and
  contraposed to itself, and **⋄-positive** when `f = gg` for a
  ⋄-self-adjoint `g` — so the square root `g` is pure, and `f` is pure with
  it;
* eff.tex **206II**.4 calls an endomap ⋄-self-adjoint when `f^⋄ = f_⋄`,
  *without* purity — which is why it has to ask separately that a
  ⋄-positive `f` be pure: "a pure endomap `f` is ⋄-positive if `f = g ∘ g`
  for some ⋄-self-adjoint `g`".

The effectus notion is therefore *formally weaker*: it does not ask the
square root `g` to be pure.  Uniqueness of `asrt_p` in 211II.1 is a
statement about the *larger* class, and 105V proves it only for the
smaller.  Everything below is the reduction of 211IV to that one missing
step; `su_contraposed_of_diamondSelfAdjoint` and `su_procPure_of_isPure`
are the two halves of the translation of proc.tex 103I's ⋄-positivity into
the effectus's, and `su_asrt_unique_of_pure_sqrt` is uniqueness once a pure
square root is available.  See the doc comment of `vn_is_andthen_eff` and
`QUESTIONS.md` **B15**.

(That the gap is not vacuous, and not a defect of the *theorem*: for a
self-adjoint non-positive `b`, `ad_b` is pure and contraposed to itself with
`ad_b(1) = b²`, yet `ad_b ≠ ad_{|b|}` — so a ⋄-self-adjoint square root that
is allowed to be impure would break uniqueness outright.  What has to be
shown is that no such square root exists; for `𝒜 = M₂` one can check by
hand that it does not.) -/

/-- **206II/101VI at `vNᵒᵖ`**: an effectus-⋄-self-adjoint endomap is
*contraposed to itself* in the sense of proc.tex **101VI**.  By **207III**
`diamond_adjunction`, `f^⋄ = f_⋄` says exactly that `f^⋄` is symmetric, and
`su_diaPull_val` turns `f^⋄` into `⌈f(·)⌉`. -/
theorem su_contraposed_of_diamondSelfAdjoint {X : WStarCPSU.{u}ᵒᵖ}
    {g : X ⟶ X} (hg : DiamondSelfAdjoint g) :
    Theses.A.Proc.Contraposed g.unop.toNCPMap g.unop.toNCPMap := by
  have hg' : diaPull g = diaPush g := hg
  have key : ∀ ps pt : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
      (ceilPred (g ≫ ps) ≼ EffectAlgebra.orth pt ↔
        Theses.A.VN.ceil (g.unop.toNCPMap (suPredVal ps))
          ≤ 1 - suPredVal pt) := by
    intro ps pt
    refine Iff.trans (su_pred_le_iff (ceilPred (g ≫ ps)) (EffectAlgebra.orth pt)) ?_
    rw [su_ceilPred_val, suPredVal_comp,
      show suPredVal (EffectAlgebra.orth pt) = 1 - suPredVal pt from
        suPredVal_orth pt]
  have hsymm : ∀ ps pt : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ), IsSharp ps → IsSharp pt →
      (ceilPred (g ≫ ps) ≼ EffectAlgebra.orth pt ↔
        ceilPred (g ≫ pt) ≼ EffectAlgebra.orth ps) := by
    intro ps pt hps hpt
    have h := diamond_adjunction g ⟨ps, hps⟩ ⟨pt, hpt⟩
    rw [← hg'] at h
    exact h
  intro s t hs ht
  obtain ⟨ps, hps⟩ := su_pred_exists (X := X) hs.nonneg hs.le_one
  obtain ⟨pt, hpt⟩ := su_pred_exists (X := X) ht.nonneg ht.le_one
  have hss : IsSharp ps := (su_isSharp_iff ps).mpr (by rw [hps]; exact hs)
  have hst : IsSharp pt := (su_isSharp_iff pt).mpr (by rw [hpt]; exact ht)
  have h := hsymm ps pt hss hst
  rw [key ps pt, key pt ps] at h
  show Theses.A.VN.ceil (g.unop.toNCPMap s) ≤ 1 - t ↔
    Theses.A.VN.ceil (g.unop.toNCPMap t) ≤ 1 - s
  rw [← hps, ← hpt]
  exact h

/-- **211II at `vNᵒᵖ`**, the *uniqueness* half of `existsUnique_asrt`, under
the one hypothesis that eff.tex **206II**.4 does not supply: that the
⋄-self-adjoint square root may be taken **pure**.  With it, `k`'s ncpsu-map
is ⋄-positive in the sense of proc.tex **103I**, and **105V**
`positive-map-uniqueness` gives `k = ad_{√a}`. -/
theorem su_asrt_unique_of_pure_sqrt {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) {k g : X ⟶ X}
    (hgpure : IsPure g) (hgsa : DiamondSelfAdjoint g) (hkg : k = g ≫ g)
    (hk1 : k ≫ truth X = p) (x : X.unop.base.carrier) :
    k.unop.toNCPMap x
      = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p) := by
  have hdp : Theses.A.Proc.IsDiamondPositive k.unop.toNCPMap := by
    refine ⟨g.unop.toNCPMap, ⟨su_procPure_of_isPure hgpure,
      su_contraposed_of_diamondSelfAdjoint hgsa⟩, ?_⟩
    refine DFunLike.ext _ _ fun y => ?_
    rw [Theses.A.Proc.ncpComp_apply]
    exact (suop_congr hkg y).trans (suop_comp_apply g g y)
  have ha : k.unop.toNCPMap (1 : X.unop.base.carrier) = suPredVal p := by
    have h := congrArg suPredVal hk1
    rwa [suPredVal_comp, suPredVal_truth] at h
  have h := Theses.A.Proc.positive_map_uniqueness
    (k.unop.toNCPMap (1 : X.unop.base.carrier))
    (ncpsu_nonneg k.unop zero_le_one) k.unop.toNCPMap hdp rfl x
  rwa [ha] at h

/-- **211IV at `vNᵒᵖ`** (`vn-is-andthen-eff`, eff.tex:4859) — *everything
except* the purity of the ⋄-self-adjoint square root.  Both axioms of
**211II** are proved here: the second outright
(`su_quot_after_compr_pure`, which is eff.tex:4862's citation of **100III**
`pure-fundamental`), the first from `su_exists_asrt` and
`su_asrt_unique_of_pure_sqrt`, given the hypothesis `H` that a
⋄-self-adjoint `g` whose square is pure has a *pure* ⋄-self-adjoint square
root with the same square. -/
theorem su_andThenEffectus_of_pure_sqrt
    (H : ∀ {X : WStarCPSU.{u}ᵒᵖ} (g : X ⟶ X), DiamondSelfAdjoint g →
      IsPure (g ≫ g) →
      ∃ h : X ⟶ X, IsPure h ∧ DiamondSelfAdjoint h ∧ g ≫ g = h ≫ h) :
    AndThenEffectus (WStarCPSU.{u}ᵒᵖ) :=
  { ‹DiamondEffectus (WStarCPSU.{u}ᵒᵖ)› with
    existsUnique_asrt := by
      intro X p
      obtain ⟨k, hkpos, hk1, hkval⟩ := su_exists_asrt p
      refine ⟨k, ⟨hkpos, hk1⟩, ?_⟩
      rintro k' ⟨⟨hk'pure, g, hgsa, hk'g⟩, hk'1⟩
      obtain ⟨h, hhpure, hhsa, hgh⟩ :=
        H g hgsa (by rw [← hk'g]; exact hk'pure)
      refine suop_hom_ext fun x => ?_
      rw [hkval x]
      exact su_asrt_unique_of_pure_sqrt p hhpure hhsa (hk'g.trans hgh) hk'1 x
    quot_after_compr_pure := fun π ξ hπ hξ => su_quot_after_compr_pure π ξ hπ hξ }

end ProcPurity

section AndThenVN

variable [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **211IV at `vNᵒᵖ`** (`vn-is-andthen-eff`, eff.tex:4859), the half that
does not need 105V: **`asrt_p` is `ad_{√a}`**, `b ↦ √a b √a`, where
`a = suPredVal p`.  By 211II `asrt_p` is the *unique* ⋄-positive map with
`1 ∘ asrt_p = p`, and `su_exists_asrt` produces `ad_{√a}` as one. -/
theorem su_asrt_apply {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (x : X.unop.base.carrier) :
    (asrt p).unop.toNCPMap x
      = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p) := by
  obtain ⟨k, hpos, h1, hk⟩ := su_exists_asrt p
  rw [← asrt_unique p k hpos h1, hk]

end AndThenVN

/-! ### The order correspondence of 223VI

The three remaining ingredients are the dictionary between the effectus
notions of 223V and the Paschke correspondence **157IV** of `B/Dils`:

* `↓f` is the ncp-interval `[0, φ]_ncp` (`su_below_iff`);
* a dilation in `vNᵒᵖ` *is* a Paschke dilation (`su_isPaschke_of_isDilation`,
  the converse reading of `su_isDilation_of_paschke`);
* `Inv ϱ = [0,1]_{ϱ(𝒜)^□}` (**223III** `su_invSet_iff`), whose ⇐ half is the
  computation `√t ϱ(b) √t + √(1−t) ϱ(b) √(1−t) = ϱ(b)` and whose ⇒ half is
  157IV applied to the Paschke dilation `(𝒫, ϱ, id)` of an nmiu-map. -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- An **nmiu**-map is its own Paschke dilation, with `h = id`: used for the
⇒ half of **223III**. -/
theorem su_paschke_nmiu {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [Theses.VonNeumannAlgebra A] [Theses.VonNeumannAlgebra B]
    (ρ : Theses.NMIUMap A B) (φ : Theses.NCPMap A B) (hφ : ∀ a, φ a = ρ a) :
    Theses.B.Dils.IsPaschkeDilationOf
      ⟨B, inferInstance, ρ, Theses.A.Proc.ncpId B⟩ ⇑φ := by
  constructor
  · intro a
    rw [show (Theses.A.Proc.ncpId B) (ρ a) = ρ a from Theses.A.Proc.ncpId_apply _,
      hφ]
  · intro D' hD'
    refine ⟨D'.h, ⟨fun a => ?_, fun c => ?_⟩, ?_⟩
    · rw [hD' a, hφ]
    · exact Theses.A.Proc.ncpId_apply _
    · rintro k ⟨-, hk2⟩
      refine DFunLike.ext _ _ fun c => ?_
      exact (Theses.A.Proc.ncpId_apply (k c)).symm.trans (hk2 c)

/-- **223V at `vNᵒᵖ`**: the down-set `↓f` of a morphism is the ncp-interval
`[0, φ]_ncp` of **157II**.  223V (eff.tex:7076) is the *Definition* of the
down-set and of "has the order correspondence"; this identification at
`vNᵒᵖ` is supplied.  (One direction needs that the difference of a subunital
map and a smaller one is again *subunital*, which it is because
`δ(1) ≤ φ(1) ≤ 1`.) -/
theorem su_below_iff {X Y : WStarCPSU.{u}ᵒᵖ} (f g : X ⟶ Y) :
    g ≼ f ↔ ⇑g.unop.toNCPMap ∈ Theses.B.Dils.ncpInterval ⇑f.unop.toNCPMap := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨g.unop.toNCPMap, fun a => (zero_add _).symm⟩,
      r.unop.toNCPMap, fun a => rfl⟩
  · rintro ⟨-, δ, hδ⟩
    have hδ1 : δ (1 : Y.unop.base.carrier) ≤ 1 := by
      refine le_trans (le_add_of_nonneg_left (ncpsu_one_nonneg g.unop)) ?_
      rw [← hδ 1]
      exact f.unop.subunital'
    obtain ⟨r, hrv⟩ : ∃ r : X ⟶ Y, r.unop.toNCPMap = δ :=
      ⟨Quiver.Hom.op ⟨δ, hδ1⟩, rfl⟩
    have hperp : Perp g r := by
      show g.unop.toNCPMap 1 + r.unop.toNCPMap 1 ≤ 1
      rw [hrv, ← hδ 1]
      exact f.unop.subunital'
    refine ⟨r, hperp, suop_hom_ext fun a => ?_⟩
    show g.unop.toNCPMap a + r.unop.toNCPMap a = f.unop.toNCPMap a
    rw [hrv, ← hδ a]

section Paschke223

variable [DiamondEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **221II at `vNᵒᵖ`**, the converse reading of `su_isDilation_of_paschke`:
a dilation of `f` in `vN_cpsuᵒᵖ` *is* a Paschke dilation of the ncp-map
`f`.  (The `h'` of a Paschke competitor is automatically subunital, being
`h'(1) = h'(ϱ'(1)) = f(1) ≤ 1`, and its mediating map is automatically
unital — so the two universal properties quantify over the same data.) -/
theorem su_isPaschke_of_isDilation {X Y P : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y)
    (ϱ : P ⟶ Y) (h : X ⟶ P) (hd : IsDilation f ϱ h)
    (ρ : Theses.NMIUMap Y.unop.base.carrier P.unop.base.carrier)
    (hρ : ∀ a, ρ a = ϱ.unop.toNCPMap a) :
    Theses.B.Dils.IsPaschkeDilationOf
      ⟨P.unop.base.carrier, inferInstance, ρ, h.unop.toNCPMap⟩
      ⇑f.unop.toNCPMap := by
  obtain ⟨hs, ht, hp, hfac, huniv⟩ := hd
  constructor
  · intro a
    show h.unop.toNCPMap (ρ a) = f.unop.toNCPMap a
    rw [hρ a, ← suop_comp_apply h ϱ a, hfac]
  · intro D' hD'
    letI := D'.vn
    have hD'ρ1 : D'.ρ (1 : Y.unop.base.carrier) = (1 : D'.P) :=
      map_one D'.ρ.toStarAlgHom
    have hρ1 : ρ (1 : Y.unop.base.carrier) = (1 : P.unop.base.carrier) :=
      map_one ρ.toStarAlgHom
    obtain ⟨g', hg'⟩ := su_exists_ncpsu_of_nmiu D'.ρ
    obtain ⟨ϱ', hϱ'⟩ : ∃ ϱ' : Opposite.op (WStarCPSU.of (WStar.of D'.P)) ⟶ Y,
        ∀ a, ϱ'.unop.toNCPMap a = D'.ρ a :=
      ⟨Quiver.Hom.op g', fun a => (hg' a)⟩
    have hh'1 : D'.h (1 : D'.P) ≤ 1 := by
      have e : D'.h (1 : D'.P) = f.unop.toNCPMap (1 : Y.unop.base.carrier) := by
        rw [← hD'ρ1]; exact hD' 1
      rw [e]
      exact f.unop.subunital'
    obtain ⟨h', hh'⟩ : ∃ h' : X ⟶ Opposite.op (WStarCPSU.of (WStar.of D'.P)),
        h'.unop.toNCPMap = D'.h :=
      ⟨Quiver.Hom.op ⟨D'.h, hh'1⟩, rfl⟩
    obtain ⟨hs', ht'⟩ := su_sharp_total_of_nmiu ϱ' D'.ρ fun a => (hϱ' a).symm
    have hfac' : h' ≫ ϱ' = f := by
      refine suop_hom_ext fun a => ?_
      rw [suop_comp_apply, hϱ', hh']
      exact hD' a
    obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := huniv ϱ' h' hs' ht' hfac'
    refine ⟨σ.unop.toNCPMap, ⟨fun a => ?_, fun c => ?_⟩, ?_⟩
    · have e := congrArg (fun m : P ⟶ Y => m.unop.toNCPMap a) hσ2
      simp only [suop_comp_apply] at e
      rw [hϱ'] at e
      rw [hρ a]
      exact e
    · have e0 : (h ≫ σ).unop.toNCPMap c = h'.unop.toNCPMap c :=
        congrArg (fun m : X ⟶ Opposite.op (WStarCPSU.of (WStar.of D'.P)) =>
          m.unop.toNCPMap c) hσ1
      exact ((suop_comp_apply h σ c).symm.trans e0).trans
        (congrArg (fun m => m c) hh')
    · rintro k ⟨hk1, hk2⟩
      have hk1' : k (1 : D'.P) ≤ 1 := by
        have e : k (1 : D'.P) = (1 : P.unop.base.carrier) := by
          rw [← hD'ρ1, hk1 1, hρ1]
        rw [e]
      obtain ⟨κ, hκ⟩ : ∃ κ : P ⟶ Opposite.op (WStarCPSU.of (WStar.of D'.P)),
          κ.unop.toNCPMap = k :=
        ⟨Quiver.Hom.op ⟨k, hk1'⟩, rfl⟩
      have hκ1 : h ≫ κ = h' := by
        refine suop_hom_ext fun c => ?_
        exact Eq.trans (suop_comp_apply h κ c)
          (Eq.trans (congrArg (fun z => h.unop.toNCPMap z)
              (congrArg (fun m => m c) hκ))
            ((hk2 c).trans (congrArg (fun m => m c) hh').symm))
      have hκ2 : κ ≫ ϱ' = ϱ := by
        refine suop_hom_ext fun a => ?_
        have hk1a : k (D'.ρ a) = ρ a := hk1 a
        exact Eq.trans (suop_comp_apply κ ϱ' a)
          (Eq.trans (congrArg (fun z => κ.unop.toNCPMap z) (hϱ' a))
            (Eq.trans (congrArg (fun m => m (D'.ρ a)) hκ)
              (hk1a.trans (hρ a))))
      exact hκ.symm.trans (congrArg
        (fun m : P ⟶ Opposite.op (WStarCPSU.of (WStar.of D'.P)) =>
          m.unop.toNCPMap) (hσu κ ⟨hκ1, hκ2⟩))

end Paschke223

section AndThen223

variable [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **223II at `vNᵒᵖ`**: the side-effect map is
`sef_p(b) = √a b √a + √(1−a) b √(1−a)` (the sum of the PCM being pointwise
addition).  223II (eff.tex:7038) is the *Definition* of
`sef_p = asrt_p ⋎ asrt_{pᗮ}`; this is its concrete value at `vNᵒᵖ`, the
computation eff.tex performs inside the proof of **223III**. -/
theorem su_sef_apply {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) (x : X.unop.base.carrier) :
    (sef p).unop.toNCPMap x
      = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p)
        + CFC.sqrt (1 - suPredVal p) * x * CFC.sqrt (1 - suPredVal p) := by
  have e : (sef p).unop.toNCPMap x
      = (asrt p).unop.toNCPMap x
        + (asrt (EffectAlgebra.orth p)).unop.toNCPMap x := rfl
  rw [e, su_asrt_apply, su_asrt_apply,
    show suPredVal (EffectAlgebra.orth p) = 1 - suPredVal p from suPredVal_orth p]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
private theorem su_sqrtConj_self {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {b : A} (hb : 0 ≤ b) :
    CFC.sqrt b * b * CFC.sqrt b = b * b := by
  have hc : CFC.sqrt b * b = b * CFC.sqrt b :=
    (Commute.cfcₙ_nnreal (rfl : b * b = b * b) NNReal.sqrt :
      Commute (CFC.sqrt b) b)
  rw [hc, mul_assoc, CFC.sqrt_mul_sqrt_self b hb]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
private theorem su_ad_sq {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (u x : A) : u * (u * x * u) * u = u * u * x * (u * u) := by
  noncomm_ring

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
private theorem su_ad_nest {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (v u x : A) :
    v * (u * (u * (v * x * v) * u) * u) * v
      = v * (u * u) * v * x * (v * (u * u) * v) := by
  noncomm_ring

/-- **211II at `vNᵒᵖ`**: the sequential conjunction is
`p & q = √a b √a`, the sequential product of 225V. -/
theorem su_andThen_val {X : WStarCPSU.{u}ᵒᵖ}
    (p q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    suPredVal (andThen p q)
      = CFC.sqrt (suPredVal p) * suPredVal q * CFC.sqrt (suPredVal p) := by
  show suPredVal (asrt p ≫ q) = _
  rw [suPredVal_comp, su_asrt_apply]

/-- **215V**.1 at `vNᵒᵖ` (the first axiom of a †'-effectus): every predicate
has a **unique** square root for `&`, namely the one naming `√a`
(`CFC.sqrt_unique`). -/
theorem su_sqrt_existsUnique {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃! q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ), andThen q q = p := by
  have ha0 : (0 : X.unop.base.carrier) ≤ suPredVal p := suPredVal_nonneg p
  have ha1 : suPredVal p ≤ 1 := suPredVal_le_one p
  have hsq := Theses.A.VN.sqrt_mem_effects (A := X.unop.base.carrier)
    ⟨ha0, ha1⟩
  obtain ⟨q₀, hq₀⟩ := su_pred_exists (X := X) hsq.1 hsq.2
  refine ⟨q₀, ?_, ?_⟩
  · refine su_pred_ext ?_
    rw [su_andThen_val, hq₀, su_sqrtConj_self (CFC.sqrt_nonneg _),
      CFC.sqrt_mul_sqrt_self _ ha0]
  · intro q hq
    refine su_pred_ext ?_
    rw [hq₀]
    have h := congrArg suPredVal hq
    rw [su_andThen_val, su_sqrtConj_self (suPredVal_nonneg q)] at h
    exact (CFC.sqrt_unique h (suPredVal_nonneg q)).symm

/-- **215V**.2 at `vNᵒᵖ` (the second axiom of a †'-effectus):
`asrt²_{p & q} = asrt_p ∘ asrt²_q ∘ asrt_p`.  Both sides are `x ↦ c x c` for
`c = √a b √a`, by `su_asrt_apply` and `√c √c = c`. -/
theorem su_asrt_sq {X : WStarCPSU.{u}ᵒᵖ}
    (p q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    asrt (andThen p q) ≫ asrt (andThen p q)
      = asrt p ≫ asrt q ≫ asrt q ≫ asrt p := by
  have hc0 : (0 : X.unop.base.carrier) ≤ CFC.sqrt (suPredVal p)
      * suPredVal q * CFC.sqrt (suPredVal p) := by
    rw [← su_andThen_val]
    exact suPredVal_nonneg _
  refine suop_hom_ext fun x => ?_
  simp only [suop_comp_apply, su_asrt_apply, su_andThen_val]
  rw [su_ad_sq, su_ad_nest, CFC.sqrt_mul_sqrt_self _ hc0,
    CFC.sqrt_mul_sqrt_self _ (suPredVal_nonneg q)]

/-- If the effect `a` named by `p` commutes with the image of `ϱ`, then
`asrt_p` acts on that image as multiplication by `a`:
`√a ϱ(b) √a = a ϱ(b)`. -/
theorem su_asrt_comp_of_commute {P Y : WStarCPSU.{u}ᵒᵖ} (ϱ : P ⟶ Y)
    (q : P ⟶ effObj (WStarCPSU.{u}ᵒᵖ))
    (hcomm : ∀ a : Y.unop.base.carrier,
      suPredVal q * ϱ.unop.toNCPMap a = ϱ.unop.toNCPMap a * suPredVal q)
    (a : Y.unop.base.carrier) :
    (asrt q).unop.toNCPMap (ϱ.unop.toNCPMap a)
      = suPredVal q * ϱ.unop.toNCPMap a := by
  have hsq : CFC.sqrt (suPredVal q) * ϱ.unop.toNCPMap a
      = ϱ.unop.toNCPMap a * CFC.sqrt (suPredVal q) :=
    (Commute.cfcₙ_nnreal (hcomm a) NNReal.sqrt :
      Commute (CFC.sqrt (suPredVal q)) (ϱ.unop.toNCPMap a))
  rw [su_asrt_apply]
  calc CFC.sqrt (suPredVal q) * ϱ.unop.toNCPMap a * CFC.sqrt (suPredVal q)
      = ϱ.unop.toNCPMap a
          * (CFC.sqrt (suPredVal q) * CFC.sqrt (suPredVal q)) := by
        rw [← mul_assoc, ← hsq, mul_assoc]
    _ = ϱ.unop.toNCPMap a * suPredVal q := by
        rw [CFC.sqrt_mul_sqrt_self _ (suPredVal_nonneg q)]
    _ = suPredVal q * ϱ.unop.toNCPMap a := (hcomm a).symm

/-- **223III** (`eff-inv-lemma`, eff.tex:7053, Lemma): in `vNᵒᵖ`, for an
nmiu-map `ϱ : 𝒜 → 𝒫`, `Inv ϱ` is the set of effects of the commutant
`ϱ(𝒜)^□` of the image.

The author's proof, transcribed.  (⇐) is the computation
`√a ϱ(b) √a + √(1−a) ϱ(b) √(1−a) = a ϱ(b) + (1−a) ϱ(b) = ϱ(b)`.  (⇒) uses
that `(𝒫, ϱ, id)` is a Paschke dilation of `ϱ` (`su_paschke_nmiu`) and
**157IV**.3 `paschke_correspondence_surjective`: `asrt_a ∘ ϱ ≤_ncp ϱ`, so
`asrt_a(ϱ(b)) = t ϱ(b)` for a `t` in the commutant, and `b = 1` gives
`a = t`. -/
theorem su_invSet_iff {P Y : WStarCPSU.{u}ᵒᵖ} (ϱ : P ⟶ Y)
    (ρ : Theses.NMIUMap Y.unop.base.carrier P.unop.base.carrier)
    (hρ : ∀ a, ρ a = ϱ.unop.toNCPMap a)
    (p : P ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    sef p ≫ ϱ = ϱ ↔ suPredVal p ∈ Theses.A.VN.commutant P.unop.base.carrier
      (Set.range ⇑ρ) := by
  have hρ1 : ρ (1 : Y.unop.base.carrier) = (1 : P.unop.base.carrier) :=
    map_one ρ.toStarAlgHom
  have ht0 : (0 : P.unop.base.carrier) ≤ suPredVal p := suPredVal_nonneg p
  have ht1 : suPredVal p ≤ 1 := suPredVal_le_one p
  constructor
  · -- ⇒
    intro hsef
    obtain ⟨φsu, hφsu⟩ := su_exists_ncpsu_of_nmiu ρ
    have hD := su_paschke_nmiu ρ φsu.toNCPMap hφsu
    -- `asrt_p ∘ ϱ` is ncp-below `ϱ`
    have hmem : ⇑(asrt p ≫ ϱ).unop.toNCPMap ∈
        Theses.B.Dils.ncpInterval ⇑φsu.toNCPMap := by
      refine ⟨⟨(asrt p ≫ ϱ).unop.toNCPMap, fun a => (zero_add _).symm⟩,
        (asrt (EffectAlgebra.orth p) ≫ ϱ).unop.toNCPMap, fun a => ?_⟩
      have e := congrArg (fun m : P ⟶ Y => m.unop.toNCPMap a) hsef
      simp only [suop_comp_apply] at e
      show φsu.toNCPMap a = (asrt p ≫ ϱ).unop.toNCPMap a
        + (asrt (EffectAlgebra.orth p) ≫ ϱ).unop.toNCPMap a
      rw [suop_comp_apply, suop_comp_apply, hφsu, hρ]
      exact e.symm
    obtain ⟨s, hs, hs0, hs1, hsval⟩ :=
      Theses.B.Dils.paschke_correspondence_surjective φsu.toNCPMap _ hD _ hmem
    -- `s = a`, by evaluating at `1`
    have hval1 : s = suPredVal p := by
      have e := congrFun hsval (1 : Y.unop.base.carrier)
      show s = suPredVal p
      have e1 : Theses.A.Proc.ncpId P.unop.base.carrier (s * ρ 1) = s := by
        rw [Theses.A.Proc.ncpId_apply, hρ1, mul_one]
      have e2 : (asrt p ≫ ϱ).unop.toNCPMap (1 : Y.unop.base.carrier)
          = suPredVal p := by
        rw [suop_comp_apply, su_asrt_apply,
          show ϱ.unop.toNCPMap (1 : Y.unop.base.carrier)
            = (1 : P.unop.base.carrier) from (hρ 1).symm.trans hρ1,
          mul_one, CFC.sqrt_mul_sqrt_self _ ht0]
      exact (e1.symm.trans e).trans e2
    rw [← hval1]
    exact hs
  · -- ⇐
    intro hcomm
    have hc : ∀ a : Y.unop.base.carrier,
        suPredVal p * ϱ.unop.toNCPMap a = ϱ.unop.toNCPMap a * suPredVal p := by
      intro a
      have h := hcomm (ϱ.unop.toNCPMap a) ⟨a, hρ a⟩
      exact h.symm
    have hco : ∀ a : Y.unop.base.carrier,
        (1 - suPredVal p) * ϱ.unop.toNCPMap a
          = ϱ.unop.toNCPMap a * (1 - suPredVal p) := by
      intro a
      rw [sub_mul, mul_sub, one_mul, mul_one, hc a]
    obtain ⟨p', hp'⟩ : ∃ p' : P ⟶ effObj (WStarCPSU.{u}ᵒᵖ),
        p' = EffectAlgebra.orth p := ⟨_, rfl⟩
    have hp'val : suPredVal p' = 1 - suPredVal p := by
      rw [hp']; exact suPredVal_orth p
    refine suop_hom_ext fun a => ?_
    have e1 : (asrt p).unop.toNCPMap (ϱ.unop.toNCPMap a)
        = suPredVal p * ϱ.unop.toNCPMap a :=
      su_asrt_comp_of_commute ϱ p hc a
    have e2 : (asrt p').unop.toNCPMap (ϱ.unop.toNCPMap a)
        = (1 - suPredVal p) * ϱ.unop.toNCPMap a := by
      refine Eq.trans (su_asrt_comp_of_commute ϱ p' (by rw [hp'val]; exact hco) a) ?_
      rw [hp'val]
    have e3 : (sef p ≫ ϱ).unop.toNCPMap a
        = (asrt p).unop.toNCPMap (ϱ.unop.toNCPMap a)
          + (asrt p').unop.toNCPMap (ϱ.unop.toNCPMap a) := by
      rw [hp']
      exact suop_comp_apply (sef p) ϱ a
    rw [e3, e1, e2, sub_mul, one_mul]
    abel

/-- **223VI at `vNᵒᵖ`** (eff.tex:7095, Example): **every dilation in `vNᵒᵖ`
has the order correspondence.**  eff.tex's proof is one line — "by
`paschke-correspondence`" — and this is what it amounts to: the dilation is a
Paschke dilation (`su_isPaschke_of_isDilation`), `↓f` is `[0,φ]_ncp`
(`su_below_iff`), `Inv ϱ` is `[0,1]_{ϱ(𝒜)^□}` (**223III** `su_invSet_iff`),
and `ϱ ∘ asrt_q ∘ h` is `φ_t` for `t` the effect named by `q`
(`su_asrt_apply` plus the commutation).  The order isomorphism is then
**157IV**: `t ↦ φ_t` is an order embedding (part 2) onto `[0,φ]_ncp`
(part 3), and `Θ` is its inverse. -/
theorem su_dilation_order_correspondence {X Y P : WStarCPSU.{u}ᵒᵖ}
    (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P) (hd : IsDilation f ϱ h) :
    DilationOrderCorrespondence f ϱ h := by
  obtain ⟨ρ, hρ⟩ := su_exists_nmiu_of_sharp_total ϱ hd.1 hd.2.1
  have hD := su_isPaschke_of_isDilation f ϱ h hd ρ hρ
  -- the effects of `Inv ϱ` commute with the image of `ϱ` (223III)
  have hcm : ∀ q : (InvSet ϱ), suPredVal q.1 ∈
      Theses.A.VN.commutant P.unop.base.carrier (Set.range ⇑ρ) :=
    fun q => (su_invSet_iff ϱ ρ hρ q.1).mp q.2
  have hcomm : ∀ (q : (InvSet ϱ)) (a : Y.unop.base.carrier),
      suPredVal q.1 * ϱ.unop.toNCPMap a
        = ϱ.unop.toNCPMap a * suPredVal q.1 :=
    fun q a => (hcm q (ϱ.unop.toNCPMap a) ⟨a, hρ a⟩).symm
  -- `ϱ ∘ asrt_q ∘ h` is `φ_t`
  have hphiT : ∀ q : (InvSet ϱ), ⇑(h ≫ asrt q.1 ≫ ϱ).unop.toNCPMap
      = Theses.B.Dils.phiT
          (⟨P.unop.base.carrier, inferInstance, ρ, h.unop.toNCPMap⟩ :
            Theses.B.Dils.PaschkeTriple Y.unop.base.carrier X.unop.base.carrier)
          (suPredVal q.1) := by
    intro q
    funext a
    show (h ≫ asrt q.1 ≫ ϱ).unop.toNCPMap a
      = h.unop.toNCPMap (suPredVal q.1 * ρ a)
    rw [suop_comp_apply, suop_comp_apply,
      su_asrt_comp_of_commute ϱ q.1 (hcomm q) a, hρ a]
  have hncp : ∀ q : (InvSet ϱ), Theses.B.Dils.NCPLe (fun _ => 0)
      (Theses.B.Dils.phiT
        (⟨P.unop.base.carrier, inferInstance, ρ, h.unop.toNCPMap⟩ :
          Theses.B.Dils.PaschkeTriple Y.unop.base.carrier X.unop.base.carrier)
        (suPredVal q.1)) := by
    intro q
    exact ⟨(h ≫ asrt q.1 ≫ ϱ).unop.toNCPMap,
      fun a => (congrFun (hphiT q) a).symm.trans (zero_add _).symm⟩
  -- the map `Θ⁻¹ : Inv ϱ → ↓f`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (InvSet ϱ) → (belowSet f),
      ∀ q, (Ψ q).1 = h ≫ asrt q.1 ≫ ϱ := by
    refine ⟨fun q => ⟨h ≫ asrt q.1 ≫ ϱ, ?_⟩, fun _ => rfl⟩
    refine (su_below_iff f _).mpr ?_
    rw [hphiT q]
    exact Theses.B.Dils.paschke_correspondence_mem f.unop.toNCPMap _ hD
      (suPredVal q.1) (hcm q) (suPredVal_nonneg _) (suPredVal_le_one _)
  -- it is an order embedding (157IV.2)
  have hle : ∀ q q' : (InvSet ϱ), (Ψ q).1 ≼ (Ψ q').1 ↔ q.1 ≼ q'.1 := by
    intro q q'
    have hemb := Theses.B.Dils.paschke_correspondence_embedding
      f.unop.toNCPMap _ hD (suPredVal q'.1) (suPredVal q.1) (hcm q')
      (suPredVal_nonneg _) (suPredVal_le_one _) (hcm q)
      (suPredVal_nonneg _) (suPredVal_le_one _)
    refine Iff.trans (su_below_iff (Ψ q').1 (Ψ q).1) ?_
    rw [hΨ q, hΨ q', hphiT q, hphiT q', su_pred_le_iff]
    exact ⟨fun hh => hemb.mp hh.2, fun hh => ⟨hncp q, hemb.mpr hh⟩⟩
  -- and onto (157IV.3)
  have hsurj : Function.Surjective Ψ := by
    intro g
    obtain ⟨t, ht, ht0, ht1, htval⟩ :=
      Theses.B.Dils.paschke_correspondence_surjective f.unop.toNCPMap _ hD
        ⇑g.1.unop.toNCPMap ((su_below_iff f g.1).mp g.2)
    obtain ⟨q, hq⟩ := su_pred_exists (X := P) ht0 ht1
    have hqinv : sef q ≫ ϱ = ϱ :=
      (su_invSet_iff ϱ ρ hρ q).mpr (by rw [hq]; exact ht)
    refine ⟨⟨q, hqinv⟩, Subtype.ext ?_⟩
    have e : ⇑(h ≫ asrt q ≫ ϱ).unop.toNCPMap = ⇑g.1.unop.toNCPMap := by
      rw [hphiT ⟨q, hqinv⟩, hq, htval]
    rw [hΨ ⟨q, hqinv⟩]
    exact suop_hom_ext fun a => congrFun e a
  have hinj : Function.Injective Ψ := by
    intro q q' hqq
    refine Subtype.ext (su_pred_ext (le_antisymm ?_ ?_))
    · exact (su_pred_le_iff q.1 q'.1).mp
        ((hle q q').mp (by rw [hqq]; exact pcm_preorder_refl _))
    · exact (su_pred_le_iff q'.1 q.1).mp
        ((hle q' q).mp (by rw [hqq]; exact pcm_preorder_refl _))
  obtain ⟨E, hE⟩ : ∃ E : (InvSet ϱ) ≃ (belowSet f), ∀ q, E q = Ψ q :=
    ⟨Equiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun _ => rfl⟩
  have hEs : ∀ g : (belowSet f), (Ψ (E.symm g)).1 = g.1 := fun g =>
    congrArg Subtype.val ((hE (E.symm g)).symm.trans (E.apply_symm_apply g))
  refine ⟨E.symm, fun g₁ g₂ => ?_, fun g => ?_⟩
  · rw [← hEs g₁, ← hEs g₂]
    exact hle _ _
  · rw [← hEs g, hΨ]

/-- **215V**.3 at `vNᵒᵖ` (the third axiom of a †'-effectus): a quotient for
a **sharp** predicate is a sharp map.  Quotients are unique up to isomorphism
(**197V**.2), so it is enough for the standard one, which for a projection
`z` is `b ↦ (1−z) b (1−z) : (1−z)𝒜(1−z) → 𝒜` (as `√(1−z) = 1−z`) and
therefore restricts to the identity on projections. -/
theorem su_quot_sharp {X W : WStarCPSU.{u}ᵒᵖ}
    {s : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} (hs : IsSharp s) {ξ : X ⟶ W}
    (hξ : IsQuotient s ξ) : SharpMap ξ := by
  have hz : IsStarProjection (suPredVal s) := (su_isSharp_iff s).mp hs
  have hz1 : IsStarProjection (1 - suPredVal s) := hz.one_sub
  have hsq : CFC.sqrt (1 - suPredVal s) = 1 - suPredVal s :=
    CFC.sqrt_unique hz1.isIdempotentElem.eq hz1.nonneg
  have hce : Theses.A.VN.ceil (1 - suPredVal s) = 1 - suPredVal s :=
    Theses.A.VN.ceil_of_isStarProjection hz1
  letI : Theses.VonNeumannAlgebra (Theses.B.Dils.cornerSet X.unop.base.carrier
      (Theses.A.VN.ceil (1 - suPredVal s))) :=
    Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
  obtain ⟨c, hcval, hcfil⟩ := Theses.B.Dils.dils_stand_filter
    (B := X.unop.base.carrier) (1 - suPredVal s) hz1.nonneg
  obtain ⟨ξ₀, hξ₀v⟩ : ∃ ξ₀ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.ceil (1 - suPredVal s))))),
      ξ₀.unop.toNCPMap = c :=
    ⟨Quiver.Hom.op ⟨c, le_trans hcfil.2.1 (sub_le_self 1 hz.nonneg)⟩, rfl⟩
  have hq₀ : IsQuotient s ξ₀ := by
    refine su_isQuotient_of_isFilterFor s ξ₀ ?_
    rw [hξ₀v, show suPredVal (EffectusPartialForm.orth s) = 1 - suPredVal s from
      suPredVal_orth s]
    exact hcfil
  have h0 : SharpMap ξ₀ := by
    refine (su_sharpMap_iff ξ₀).mpr fun b hb => ?_
    -- the corner element `b` is generalised to a plain `bv` before `⌈1−z⌉` is
    -- rewritten: `↑b`'s own type mentions `⌈1−z⌉`, so `rw` would not typecheck
    obtain ⟨bv, hb1, hval, hbv2⟩ : ∃ bv : X.unop.base.carrier,
        IsStarProjection bv ∧
        ξ₀.unop.toNCPMap b
          = CFC.sqrt (1 - suPredVal s) * bv * CFC.sqrt (1 - suPredVal s) ∧
        Theses.A.VN.ceil (1 - suPredVal s) * bv
            * Theses.A.VN.ceil (1 - suPredVal s) = bv :=
      ⟨b.1, ⟨congrArg Subtype.val hb.isIdempotentElem.eq,
          congrArg Subtype.val hb.isSelfAdjoint.star_eq⟩,
        Eq.trans (congrArg (fun m => m b) hξ₀v) (hcval b), b.2⟩
    rw [hce] at hbv2
    rw [hval, hsq, hbv2]
    exact hb1
  obtain ⟨θ, hiso, hθ, -⟩ := quotient_basics_2 hξ hq₀
  haveI := hiso
  rw [← hθ]
  exact sharpMap_comp h0 (sharpMap_of_isIso θ)

/-- **215V at `vNᵒᵖ`**: `vNᵒᵖ` is a **†'-effectus**. -/
theorem su_daggerPrimeEffectus : DaggerPrimeEffectus (WStarCPSU.{u}ᵒᵖ) where
  sqrt_existsUnique := su_sqrt_existsUnique
  asrt_sq := su_asrt_sq
  quot_sharp := by
    intro X W s hs ξ hq
    exact su_quot_sharp hs hq

/-- **215VI at `vNᵒᵖ`** (`vn-is-dagger-category`, eff.tex:5338, Corollary):
the &-effectus `vNᵒᵖ` is a **†-effectus**, by **220II**
`dagger_thm_sufficiency` applied to `su_daggerPrimeEffectus`. -/
theorem su_daggerEffectus : Nonempty (DaggerEffectus (WStarCPSU.{u}ᵒᵖ)) := by
  letI := su_daggerPrimeEffectus.{u}
  exact dagger_thm_sufficiency

/-! ### The dagger of `vNᵒᵖ`, concretely (215II, 215VIa)

**215II** (eff.tex:5301) and **215VIa** (eff.tex:5344, Remarks): the dagger
of `vNᵒᵖ` — which `su_daggerEffectus` above produces only as a `Nonempty`,
the corollary asserting existence — *is fixed* by two rules:

1. `ϑ† = ϑ⁻¹` for an (nmiu-)isomorphism `ϑ`, because `ϑ` is ⋄-adjoint to
   `ϑ⁻¹` and pure maps are rigid; and
2. the standard filter `c : 𝒜 → ⌈b⌉𝒜⌈b⌉` of an effect `b`, `c(a) = √b a √b`
   read as an ncp-map `⌈b⌉𝒜⌈b⌉ → 𝒜`, has as dagger
   `c† : ⌈b⌉𝒜⌈b⌉ → 𝒜` — the map `a ↦ √b a √b` read in the *other*
   direction, i.e. the corner-type ncp-map `𝒜 → ⌈b⌉𝒜⌈b⌉`.  "This follows
   from `asrt_p† = asrt_p` and `dagger-of-zeta`", and that is exactly the
   proof below.

"Fixed by" is rendered by quantifying over an arbitrary
`d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ)`: every dagger on `vNᵒᵖ` obeys the
rules, so they determine it on the pure maps (212III puts every pure map in
the form `π ∘ ϑ ∘ ζ ∘ asrt`).

The abstract halves are 216IX `dagger_of_iso` and 216VII `dagger_of_zeta`,
but the latter fixes the dagger of the **chosen** `ζ_s` only, and
`comprObj`/`comprMap`/`zetaMap` are choices from an existential, of which
nothing concrete is known at `vNᵒᵖ`.  `su_dagger_of_quotient` removes the
choice — the dagger of *any* quotient `ζ` for `sᵖ` is the map `κ` with
`ζ ≫ κ = asrt_s` — and that is what makes a computation rule possible.
`su_dagger_of_filter` is then 215VIa.2 in effectus form, through 212I's
factorisation of the standard filter as `ζ_{⌈p⌉} ∘ asrt_p`, and
`su_dagger_standard_filter` is the concrete statement at `vNᵒᵖ`.  The
second half of 215II, that `EJAᵒᵖ` is a †-effectus, is a bare citation to
other work and is out of scope; 215VIa's closing formula for a general pure
map `φ` and the `ad_T ↦ ad_{T*}` remark of the nested point 2150.72 are not
rendered — see the `215VIa` rows of `docs/audit/beff-vnexamples.csv`. -/

/-- A **pure and faithful map is a quotient** — for `(1 ∘ f)ᵖ`.  Writing
`f = π ∘ ξ` (201II), `im f ≼ im π` by 202V, so `im π = 1`; `π` is then a
comprehension for its own image `1` (202-level `isComprehension_imPred`),
hence an isomorphism, and `ξ ≫ π` is a quotient by 197V.1.  eff.tex uses
this silently; it is what identifies the concrete filters below as
quotients without a universal property having to be verified. -/
theorem su_isQuotient_of_pure_faithful {X Y : WStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hf : IsPure f) (hfaith : FaithfulMap f) :
    IsQuotient (orth (f ≫ truth Y)) f := by
  obtain ⟨W, ξ, π, p, q, hξ, hπ, rfl⟩ := hf
  -- the image of `ξ ≫ π` is `1`, images being unique
  have him : imPred (ξ ≫ π) = (1 : Pred Y) :=
    eabasics_le_antisymm ((isImage_imPred (ξ ≫ π)).2 1 hfaith.1)
      (hfaith.2 (imPred (ξ ≫ π)) (isImage_imPred (ξ ≫ π)).1)
  -- hence `im π = 1`, and `π` is a comprehension for `1`
  have himπ : imPred π = (1 : Pred Y) := by
    refine eabasics_le_antisymm (pred_le_truth _) ?_
    have h := (im_ineq π ξ).1
    rwa [him] at h
  have hπ1 : IsComprehension (1 : Pred Y) π := by
    have h := isComprehension_imPred hπ
    rwa [himπ] at h
  -- a comprehension for `1` is an isomorphism, `𝟙` being one (199VII.2, .3)
  obtain ⟨θ, hiso, hθ, -⟩ := compr_basics_2 hπ1 (compr_basics_3 (𝟙 Y))
  have := hiso
  have hπθ : π = θ := by rw [← hθ, Category.comp_id]
  have : IsIso π := by rw [hπθ]; infer_instance
  have hpq : IsQuotient p (ξ ≫ π) := quotient_basics_1 hξ π
  have htot : IsTotal π := compr_total hπ1
  have hval : (ξ ≫ π) ≫ truth Y = orth p := by
    rw [Category.assoc, htot]
    exact quotient_basics_5 hξ
  rw [hval, eabasics_orth_orth]
  exact hpq

/-- **215VIa.1** (eff.tex:5346, Remarks) at `vNᵒᵖ`: **the dagger of an
isomorphism is its inverse**.  This is 216IX `dagger_of_iso` read at
`vNᵒᵖ`, with the isomorphism presented by a two-sided inverse `g` rather
than by an `Iso` of `Pure (vNᵒᵖ)`; by 210III (`su_sharp_total_of_nmiu`,
`su_exists_nmiu_of_sharp_total`) the `f` of the statement are exactly the
nmiu-isomorphisms, which is how the thesis says it. -/
theorem su_dagger_of_iso (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X)
    (hgf : g ≫ f = 𝟙 Y) (hfp : IsPure f) :
    (d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of Y) ⟨f, hfp⟩).1 = g := by
  have : IsIso g := ⟨f, hgf, hfg⟩
  have hgp : IsPure g := isPure_of_isQuotient (quotient_basics_3 g)
  exact congrArg Subtype.val (dagger_of_iso d
    { hom := ⟨f, hfp⟩, inv := ⟨g, hgp⟩,
      hom_inv_id := Subtype.ext hfg, inv_hom_id := Subtype.ext hgf })

/-- **216VII** (`dagger-of-zeta`, eff.tex:5520) **without the choice**: the
dagger of *any* quotient `ζ` for `sᵖ` (`s` sharp) is the unique `κ` with
`ζ ≫ κ = asrt_s` — i.e. the comprehension for `s` corresponding to `ζ` by
211VII.

`dagger_of_zeta` fixes `ζ_s† = π_s` for the *chosen* pair only.  Any other
quotient for `sᵖ` is `ζ_s ≫ θ` for a unique isomorphism `θ` (197V.2), whose
dagger is `θ⁻¹` (216IX), so `ζ† = θ⁻¹ ∘ π_s`; and `κ = θ⁻¹ ∘ π_s` too,
since `ζ ≫ (θ⁻¹ ≫ π_s) = ζ_s ≫ π_s = asrt_s = ζ ≫ κ` and quotients are
epic (197V.6).  Nothing here is special to `vNᵒᵖ`; it is stated here
because this is where the computation rules of 215VIa live. -/
theorem su_dagger_of_quotient (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    {X Q : WStarCPSU.{u}ᵒᵖ} {s : Pred X} (hs : IsSharp s)
    {ζ : X ⟶ Q} (hζ : IsQuotient (orth s) ζ) (hζp : IsPure ζ)
    {κ : Q ⟶ X} (hκ : ζ ≫ κ = asrt s) :
    (d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of Q) ⟨ζ, hζp⟩).1 = κ := by
  obtain ⟨θ, hiso, hθ, -⟩ := quotient_basics_2 hζ (zetaMap_spec s hs).1
  have := hiso
  have hepi : Epi ζ := quotient_basics_6 hζ
  have hκv : κ = inv θ ≫ comprMap s := by
    refine (cancel_epi ζ).mp ?_
    rw [hκ, ← hθ, Category.assoc, ← Category.assoc θ (inv θ), IsIso.hom_inv_id,
      Category.id_comp]
    exact ((zetaMap_spec s hs).2.2).symm
  have hζ0p : IsPure (zetaMap s hs) := isPure_of_isQuotient (zetaMap_spec s hs).1
  have hθp : IsPure θ := isPure_of_isQuotient (quotient_basics_3 θ)
  -- the three maps are handed to the dagger as abstract maps of `Pure vNᵒᵖ`
  -- (the idiom of `dagger_of_zeta` itself: `⟨_, _⟩` under `dag` does not
  -- unify with a composite otherwise)
  have main : ∀ (Zm : (PureCat.of X : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of Q)
      (Zs : (PureCat.of X : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of (comprObj s))
      (Th : (PureCat.of (comprObj s) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of Q),
      Zm.1 = ζ → Zs.1 = zetaMap s hs → Th.1 = θ →
      (d.daggerCat.dag Zm).1 = κ := by
    intro Zm Zs Th hZm hZs hTh
    have hZmc : Zm = Zs ≫ Th := by
      refine Subtype.ext ?_
      show Zm.1 = Zs.1 ≫ Th.1
      rw [hZm, hZs, hTh, hθ]
    have hdTh : (d.daggerCat.dag Th).1 = inv θ := by
      have hTh' : Th = ⟨θ, hθp⟩ := Subtype.ext hTh
      rw [hTh']
      exact su_dagger_of_iso d θ (inv θ) (IsIso.hom_inv_id θ) (IsIso.inv_hom_id θ)
        hθp
    have hdZs : (d.daggerCat.dag Zs).1 = comprMap s := by
      have hZs' : Zs = ⟨zetaMap s hs, hζ0p⟩ := Subtype.ext hZs
      rw [hZs']
      exact congrArg Subtype.val (dagger_of_zeta d hs)
    rw [hZmc, d.daggerCat.dag_comp]
    show (d.daggerCat.dag Th).1 ≫ (d.daggerCat.dag Zs).1 = κ
    rw [hdTh, hdZs, hκv]
  exact main ⟨ζ, hζp⟩ ⟨zetaMap s hs, hζ0p⟩ ⟨θ, hθp⟩ rfl rfl rfl

/-- **215VIa.2** (eff.tex:5352, Remarks) in effectus form: the dagger of the
standard filter of a predicate `p` is `κ ≫ asrt_p`, where `κ` is the
comprehension for `⌈p⌉` matching the quotient `ζ`.

The standard filter is `asrt_p ≫ ζ` — 212I `zeta_asrt_quot`, the thesis's
own factorisation — so `(asrt_p ≫ ζ)† = ζ† ∘ asrt_p† = κ ∘ asrt_p`, using
`asrt_p† = asrt_p` (215I.1) and `su_dagger_of_quotient`.  That is exactly
the derivation 215VIa.2 gives: "this follows from `asrt_p† = asrt_p` and
`dagger-of-zeta`". -/
theorem su_dagger_of_filter (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    {X Q : WStarCPSU.{u}ᵒᵖ} (p : Pred X)
    {ζ : X ⟶ Q} (hζ : IsQuotient (orth (ceilPred p)) ζ) (hζp : IsPure ζ)
    {κ : Q ⟶ X} (hκ : ζ ≫ κ = asrt (ceilPred p)) (hfp : IsPure (asrt p ≫ ζ)) :
    (d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of Q)
      ⟨asrt p ≫ ζ, hfp⟩).1 = κ ≫ asrt p := by
  have main : ∀ (Fm : (PureCat.of X : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of Q)
      (Am : (PureCat.of X : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of X)
      (Zm : (PureCat.of X : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of Q),
      Fm.1 = asrt p ≫ ζ → Am.1 = asrt p → Zm.1 = ζ →
      (d.daggerCat.dag Fm).1 = κ ≫ asrt p := by
    intro Fm Am Zm hFm hAm hZm
    have hFc : Fm = Am ≫ Zm := by
      refine Subtype.ext ?_
      show Fm.1 = Am.1 ≫ Zm.1
      rw [hFm, hAm, hZm]
    have hdAm : d.daggerCat.dag Am = Am := by
      have hAm' : Am = ⟨asrt p, (asrt_spec p).1.1⟩ := Subtype.ext hAm
      rw [hAm']
      exact d.dag_asrt p
    have hdZm : (d.daggerCat.dag Zm).1 = κ := by
      have hZm' : Zm = ⟨ζ, hζp⟩ := Subtype.ext hZm
      rw [hZm']
      exact su_dagger_of_quotient d (isSharp_ceil p) hζ hζp hκ
    rw [hFc, d.daggerCat.dag_comp, hdAm]
    show (d.daggerCat.dag Zm).1 ≫ Am.1 = κ ≫ asrt p
    rw [hdZm, hAm]
  exact main ⟨asrt p ≫ ζ, hfp⟩ ⟨asrt p, (asrt_spec p).1.1⟩ ⟨ζ, hζp⟩ rfl rfl rfl

/-- **215VIa.2** (eff.tex:5352, Remarks) **at `vNᵒᵖ`, concretely**: for
every predicate `p` on `𝒜`, naming the effect `b`, the standard filter
`c : 𝒜 → ⌈b⌉𝒜⌈b⌉` — the map of `vN_cpsuᵒᵖ` whose ncp-map is
`y ↦ √b y √b : ⌈b⌉𝒜⌈b⌉ → 𝒜`, a quotient for `pᵖ` (197IV) — has as dagger
the corner-type map `c† : ⌈b⌉𝒜⌈b⌉ → 𝒜` whose ncp-map is
`a ↦ √b a √b : 𝒜 → ⌈b⌉𝒜⌈b⌉`, the *same formula in the other direction*.
`i` is the inclusion `⌈b⌉𝒜⌈b⌉ → 𝒜` of the corner, which is what makes both
formulas literal; it is injective, so it pins `c†` down.

The corner is produced here rather than quantified over because the
comprehension objects of `vNᵒᵖ` are choices from an existential: `ζ` is the
standard filter of `⌈b⌉` (the *inclusion*, `su_incl_of_ceil`), `κ` the
standard corner at `⌈b⌉` (`su_stand_corner_ceil`), and
`su_dagger_of_filter` applies to that pair. -/
theorem su_dagger_standard_filter (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    {X : WStarCPSU.{u}ᵒᵖ} (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃ (Q : WStarCPSU.{u}ᵒᵖ) (c : X ⟶ Q)
      (i : Q.unop.base.carrier → X.unop.base.carrier) (hc : IsPure c),
      Function.Injective i ∧ IsQuotient (orth p) c ∧
      (∀ y : Q.unop.base.carrier, c.unop.toNCPMap y
        = CFC.sqrt (suPredVal p) * i y * CFC.sqrt (suPredVal p)) ∧
      (∀ x : X.unop.base.carrier,
        i ((d.daggerCat.dag (X := PureCat.of X) (Y := PureCat.of Q)
            ⟨c, hc⟩).1.unop.toNCPMap x)
          = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p)) := by
  have hb0 : (0 : X.unop.base.carrier) ≤ suPredVal p := suPredVal_nonneg p
  have hb1 : suPredVal p ≤ 1 := suPredVal_le_one p
  have hcp : IsStarProjection (Theses.A.VN.ceil (suPredVal p)) :=
    (Theses.A.VN.ceil_spec hb0).1
  have hsq : CFC.sqrt (Theses.A.VN.ceil (suPredVal p))
      = Theses.A.VN.ceil (suPredVal p) :=
    CFC.sqrt_unique hcp.isIdempotentElem.eq hcp.nonneg
  obtain ⟨hs1, hs2⟩ := su_sqrt_mul_ceil (A := X.unop.base.carrier) hb0
  let _cvn : Theses.VonNeumannAlgebra (Theses.B.Dils.cornerSet X.unop.base.carrier
      (Theses.A.VN.ceil (suPredVal p))) :=
    Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
  obtain ⟨cinc, hincval, hincfil⟩ := su_incl_of_ceil (A := X.unop.base.carrier) hb0
  obtain ⟨hcor, hcorval, hcorfor⟩ :=
    su_stand_corner_ceil (A := X.unop.base.carrier) hb0
  have hcoru : hcor (1 : X.unop.base.carrier) = 1 := by
    refine Theses.B.Dils.cornerSet.val_injective ?_
    rw [hcorval, mul_one, hcp.isIdempotentElem.eq, Theses.B.Dils.cornerSet.val_one]
  obtain ⟨ζ, hζv⟩ : ∃ ζ : X ⟶ Opposite.op (WStarCPSU.of (WStar.of
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.ceil (suPredVal p))))),
      ζ.unop.toNCPMap = cinc :=
    ⟨Quiver.Hom.op ⟨cinc, by
      show cinc 1 ≤ 1
      rw [hincval, Theses.B.Dils.cornerSet.val_one]
      exact hcp.le_one⟩, rfl⟩
  obtain ⟨κ, hκv⟩ : ∃ κ : Opposite.op (WStarCPSU.of (WStar.of
        (Theses.B.Dils.cornerSet X.unop.base.carrier
          (Theses.A.VN.ceil (suPredVal p))))) ⟶ X,
      κ.unop.toNCPMap = hcor :=
    ⟨Quiver.Hom.op ⟨hcor, le_of_eq hcoru⟩, rfl⟩
  -- the inclusion is the quotient for `⌈p⌉ᵖ`
  have hval2 : suPredVal (EffectusPartialForm.orth (orth (ceilPred p)))
      = Theses.A.VN.ceil (suPredVal p) := by
    rw [show suPredVal (EffectusPartialForm.orth (orth (ceilPred p)))
        = 1 - suPredVal (orth (ceilPred p)) from suPredVal_orth _,
      show suPredVal (orth (ceilPred p)) = 1 - suPredVal (ceilPred p) from
        suPredVal_orth _, su_ceilPred_val, sub_sub_cancel]
  have hζq : IsQuotient (orth (ceilPred p)) ζ := by
    refine su_isQuotient_of_isFilterFor (orth (ceilPred p)) ζ ?_
    rw [hval2, hζv]
    exact hincfil
  have hζp : IsPure ζ := isPure_of_isQuotient hζq
  -- the standard corner is the comprehension for `⌈p⌉`
  have hκc : IsComprehension (ceilPred p) κ := by
    refine su_isComprehension_of_isCornerFor (ceilPred p) κ ?_ ?_
    · rw [hκv]; exact hcoru
    · rw [hκv, su_ceilPred_val]; exact hcorfor
  have hζκ : ζ ≫ κ = asrt (ceilPred p) := by
    refine suop_hom_ext fun x => ?_
    have e1 : ζ.unop.toNCPMap (κ.unop.toNCPMap x) = cinc (hcor x) :=
      Eq.trans (congrArg (fun m => m (κ.unop.toNCPMap x)) hζv)
        (congrArg (fun y => cinc y) (congrArg (fun m => m x) hκv))
    have e2 : cinc (hcor x) = Theses.A.VN.ceil (suPredVal p) * x
        * Theses.A.VN.ceil (suPredVal p) :=
      Eq.trans (hincval (hcor x)) (hcorval x)
    have e3 : (asrt (ceilPred p)).unop.toNCPMap x
        = Theses.A.VN.ceil (suPredVal p) * x * Theses.A.VN.ceil (suPredVal p) := by
      rw [su_asrt_apply, su_ceilPred_val, hsq]
    exact Eq.trans (suop_comp_apply ζ κ x) (Eq.trans e1 (Eq.trans e2 e3.symm))
  have hfp : IsPure (asrt p ≫ ζ) := upm_closed_pure (asrt_spec p).1.1 hζp
  have hdag := su_dagger_of_filter d p hζq hζp hζκ hfp
  -- `asrt_p ≫ ζ` is the standard filter of `b`, a quotient for `pᵖ` (212I)
  obtain ⟨c₀, hc₀val, hc₀fil⟩ :=
    Theses.B.Dils.dils_stand_filter (B := X.unop.base.carrier) (suPredVal p) hb0
  have hcc : (asrt p ≫ ζ).unop.toNCPMap = c₀ := by
    refine DFunLike.ext _ _ fun y => ?_
    have e1 : (asrt p ≫ ζ).unop.toNCPMap y
        = (asrt p).unop.toNCPMap (ζ.unop.toNCPMap y) := suop_comp_apply (asrt p) ζ y
    have e2 : ζ.unop.toNCPMap y = y.1 :=
      Eq.trans (congrArg (fun m => m y) hζv) (hincval y)
    rw [e1, e2, su_asrt_apply]
    exact (hc₀val y).symm
  have hquot : IsQuotient (orth p) (asrt p ≫ ζ) := by
    refine su_isQuotient_of_isFilterFor (orth p) (asrt p ≫ ζ) ?_
    have hval3 : suPredVal (EffectusPartialForm.orth (orth p)) = suPredVal p := by
      rw [show suPredVal (EffectusPartialForm.orth (orth p))
          = 1 - suPredVal (orth p) from suPredVal_orth _,
        show suPredVal (orth p) = 1 - suPredVal p from suPredVal_orth _,
        sub_sub_cancel]
    rw [hval3, hcc]
    exact hc₀fil
  refine ⟨_, asrt p ≫ ζ, fun y => y.1, hfp,
    Theses.B.Dils.cornerSet.val_injective, hquot, fun y => ?_, fun x => ?_⟩
  · have e1 : (asrt p ≫ ζ).unop.toNCPMap y
        = (asrt p).unop.toNCPMap (ζ.unop.toNCPMap y) := suop_comp_apply (asrt p) ζ y
    have e2 : ζ.unop.toNCPMap y = y.1 :=
      Eq.trans (congrArg (fun m => m y) hζv) (hincval y)
    rw [e1, e2, su_asrt_apply]
  · rw [hdag]
    have e2 : ((κ ≫ asrt p).unop.toNCPMap x).1
        = Theses.A.VN.ceil (suPredVal p) * ((asrt p).unop.toNCPMap x)
          * Theses.A.VN.ceil (suPredVal p) := by
      have e1 : (κ ≫ asrt p).unop.toNCPMap x
          = κ.unop.toNCPMap ((asrt p).unop.toNCPMap x) := suop_comp_apply κ (asrt p) x
      rw [e1]
      exact Eq.trans (congrArg (fun m => (m ((asrt p).unop.toNCPMap x)).1) hκv)
        (hcorval _)
    show ((κ ≫ asrt p).unop.toNCPMap x).1
      = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p)
    rw [e2, su_asrt_apply]
    calc Theses.A.VN.ceil (suPredVal p)
          * (CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p))
          * Theses.A.VN.ceil (suPredVal p)
        = (Theses.A.VN.ceil (suPredVal p) * CFC.sqrt (suPredVal p)) * x
          * (CFC.sqrt (suPredVal p) * Theses.A.VN.ceil (suPredVal p)) := by
          noncomm_ring
      _ = CFC.sqrt (suPredVal p) * x * CFC.sqrt (suPredVal p) := by rw [hs1, hs2]

end AndThen223

/-! ### `Pure (vNᵒᵖ)` has no coequalizers (224VII)

`bsols.tex`:3480 argues with `M₄`, the swap `σ` on `ℂ²⊗ℂ²`, and the
projections `p_𝒮`, `p_𝒜` onto the symmetric and the antisymmetric subspace.
Only two properties of that configuration are used: `σ` is a self-adjoint
unitary, so `σ = 2p_𝒮 − 1`, and both `p_𝒮` and `p_𝒜 = 1 − p_𝒮` are non-zero.
The argument below is the author's, run with an arbitrary such `p` in
`B(ℋ)` — the smallest instance being `ℋ = ℂ²` with `p` a rank-one
projection, which is what `su_exc_purec_equal` uses.  Three divergences from
the printed solution:

* the final contradiction uses `ad_{p}` and `ad_{1−p}` — which are pure,
  land in the two corners and are fixed by `ad_σ` — in place of
  `ad_{e†_𝒮} : M₃ → M₄` and `ad_{e†_𝒜} : ℂ → M₄`, so no three-dimensional
  subspace has to be built;
* the passage from `p ξ(c) = ξ(c) p` to `⌈ξ(1)⌉p⌈ξ(1)⌉` central, which the
  solution makes with the pseudoinverse of `√ξ(1)`, is replaced by the
  rank-one computation of `proj_mul_selfAdjoint` above, which reaches the
  same conclusion (`p√a ∈ {0, √a}`) directly;
* the range of the filter half of the pure map `e` is reached through the
  *effectus* universal property of the quotient (`su_pure_range`) rather
  than through the isomorphism `ϑ : 𝒞 → ⌈ξ(1)⌉M₄⌈ξ(1)⌉`. -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- `ad_w : b ↦ w* b w` as a morphism `X ⟶ X` of `vN_cpsuᵒᵖ`, for any `w`
with `w* w ≤ 1` (the version of `su_exists_ad` that does not ask `w ≥ 0`;
`ad_σ` for a symmetry `σ` is the point). -/
theorem su_exists_ad' {X : WStarCPSU.{u}ᵒᵖ} {w : X.unop.base.carrier}
    (hw1 : star w * w ≤ 1) :
    ∃ k : X ⟶ X, ∀ x, k.unop.toNCPMap x = star w * x * w := by
  obtain ⟨m, hm⟩ : ∃ m : Theses.NCPSUMap X.unop.base.carrier X.unop.base.carrier,
      ∀ x, m.toNCPMap x = star w * x * w := by
    refine ⟨mkNCPSU { toFun := fun x => star w * x * w
                      map_add' := fun x y => by noncomm_ring
                      map_smul' := fun c x => by simp } ?_ ?_ ?_,
      fun x => rfl⟩
    · intro n c b
      have h := ad_cp_1 w n c b
      simpa [mul_assoc] using h
    · intro Dset s' hne hdir hlub
      have hb : BddAbove Dset := ⟨s', hlub.1⟩
      have hsd : Theses.dirSup Dset ⟨hne, hdir, hb⟩ = s' :=
        (Theses.isLUB_dirSup Dset ⟨hne, hdir, hb⟩).unique hlub
      have h := Theses.A.VN.ad_normal w Dset ⟨hne, hdir, hb⟩
      rw [hsd] at h
      exact h
    · show star w * 1 * w ≤ 1
      rw [mul_one]
      exact hw1
  exact ⟨Quiver.Hom.op m, hm⟩

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- The identity of `vN_cpsuᵒᵖ` is the identity map. -/
theorem suop_id_apply {X : WStarCPSU.{u}ᵒᵖ} (a : X.unop.base.carrier) :
    (𝟙 X).unop.toNCPMap a = a := su_id_apply a

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] in
/-- A projection below an element orthogonal to it is zero. -/
theorem su_proj_eq_zero {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {z w : A} (hz : IsStarProjection z) (hle : z ≤ w)
    (hzw : z * w = 0) : z = 0 := by
  have h1 : z * z * z ≤ z * w * z := hz.isSelfAdjoint.conjugate_le_conjugate hle
  rw [hzw, zero_mul, hz.isIdempotentElem.eq, hz.isIdempotentElem.eq] at h1
  exact le_antisymm h1 hz.nonneg

/-- **Comprehensions of `vN_cpsuᵒᵖ` are surjective**: by `compr_basics_2` a
comprehension for `q` is the standard corner `h_{⌊q⌋}` of `su_exists_corner`
precomposed with an isomorphism, and the standard corner `b ↦ ⌊q⌋b⌊q⌋` is
surjective onto `⌊q⌋𝒜⌊q⌋`. -/
theorem su_compr_surjective {W X : WStarCPSU.{u}ᵒᵖ}
    {q : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} {π : W ⟶ X} (hπ : IsComprehension q π) :
    Function.Surjective π.unop.toNCPMap := by
  obtain ⟨W₀, π₀, hπ₀, -, hsurj₀, -⟩ := su_exists_corner q
  obtain ⟨θ, hiso, hθ, -⟩ := compr_basics_2 hπ hπ₀
  haveI := hiso
  intro y
  obtain ⟨x, hx⟩ := hsurj₀ ((inv θ).unop.toNCPMap y)
  refine ⟨x, ?_⟩
  have hyy : θ.unop.toNCPMap ((inv θ).unop.toNCPMap y) = y := by
    have h : (θ ≫ inv θ).unop.toNCPMap y = (𝟙 W).unop.toNCPMap y :=
      congrArg (fun m : W ⟶ W => m.unop.toNCPMap y) (IsIso.hom_inv_id θ)
    rw [suop_comp_apply, suop_id_apply] at h
    exact h
  have hππ : π.unop.toNCPMap x = θ.unop.toNCPMap (π₀.unop.toNCPMap x) := by
    have h : π.unop.toNCPMap x = (θ ≫ π₀).unop.toNCPMap x :=
      congrArg (fun m : W ⟶ X => m.unop.toNCPMap x) hθ.symm
    rw [suop_comp_apply] at h
    exact h
  rw [hππ, hx, hyy]

section PureCoequalizer

open scoped ComplexInnerProductSpace

variable [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)]

/-- **The range of a pure map** `f` of `vN_cpsuᵒᵖ` contains `√a x √a` for
every effect `x`, where `a = f(1)`.  `f` is a quotient followed by a
comprehension; the comprehension is total and surjective
(`su_compr_surjective`), and `√a x √a`, being below `a ≼ pᗮ`, is the value
at `1` of a map that the quotient's universal property factors. -/
theorem su_pure_range {X Y : WStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y} (hf : IsPure f)
    {x : X.unop.base.carrier} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ z : Y.unop.base.carrier, f.unop.toNCPMap z
      = CFC.sqrt (f.unop.toNCPMap 1) * x * CFC.sqrt (f.unop.toNCPMap 1) := by
  obtain ⟨Q, ξ, π, p₀, q₀, hξ, hπ, hfe⟩ := hf
  have hπ1 : π.unop.toNCPMap 1 = 1 := (su_isTotal_iff π).mp (compr_total hπ)
  have hsurj := su_compr_surjective hπ
  set a : X.unop.base.carrier := f.unop.toNCPMap 1 with ha
  have haξ : ξ.unop.toNCPMap 1 = a := by
    rw [ha, hfe, suop_comp_apply, hπ1]
  have ha0 : 0 ≤ a := by
    have h := ncpsu_mono f.unop (zero_le_one (α := Y.unop.base.carrier))
    rwa [ncp_zero_apply] at h
  have ha1 : a ≤ 1 := f.unop.subunital'
  have hb : ξ.unop.toNCPMap 1 ≤ suPredVal (EffectusPartialForm.orth p₀) := by
    have h1 := (su_pred_le_iff (ξ ≫ truth Q) (EffectusPartialForm.orth p₀)).mp hξ.1
    rwa [suPredVal_comp, suPredVal_truth] at h1
  set s : X.unop.base.carrier := CFC.sqrt a with hs
  have hs0 : (0 : X.unop.base.carrier) ≤ s := CFC.sqrt_nonneg a
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha0
  have hsxs0 : (0 : X.unop.base.carrier) ≤ s * x * s :=
    (IsSelfAdjoint.of_nonneg hs0).conjugate_nonneg hx0
  have hsxsle : s * x * s ≤ a := by
    have h := (IsSelfAdjoint.of_nonneg hs0).conjugate_le_conjugate hx1
    rwa [mul_one, hss] at h
  set w : X.unop.base.carrier := CFC.sqrt (s * x * s) with hw
  have hw0 : (0 : X.unop.base.carrier) ≤ w := CFC.sqrt_nonneg _
  have hww : w * w = s * x * s := CFC.sqrt_mul_sqrt_self _ hsxs0
  obtain ⟨g, hg⟩ := su_exists_ad (X := X) hw0 (by rw [hww]; exact hsxsle.trans ha1)
  have hgle : (g ≫ truth X) ≼ EffectusPartialForm.orth p₀ := by
    refine (su_pred_le_iff _ _).mpr ?_
    rw [suPredVal_comp, suPredVal_truth, hg, mul_one, hww]
    exact hsxsle.trans (haξ ▸ hb)
  obtain ⟨m, hm, -⟩ := hξ.2 g hgle
  obtain ⟨z, hz⟩ := hsurj (m.unop.toNCPMap 1)
  refine ⟨z, ?_⟩
  have hval : ξ.unop.toNCPMap (m.unop.toNCPMap 1) = s * x * s := by
    have h := congrArg (fun k : X ⟶ X => k.unop.toNCPMap (1 : X.unop.base.carrier)) hm
    simp only [suop_comp_apply] at h
    rw [h, hg, mul_one, hww]
  rw [hfe, suop_comp_apply, hz, hval]

/-- **224VII at `vNᵒᵖ`, the heart** (bsols.tex:3480): if a von Neumann
algebra `X` carries a projection `p ∉ {0,1}` for which the factoriality
input `hcore` holds, then `id` and `ad_σ`, `σ = 2p − 1`, have no
coequalizer in `Pure (vNᵒᵖ)`. -/
theorem su_no_coequalizer_of_proj {X : WStarCPSU.{u}ᵒᵖ} {p : X.unop.base.carrier}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hcore : ∀ s : X.unop.base.carrier, 0 ≤ s →
      (∀ x : X.unop.base.carrier, 0 ≤ x → x ≤ 1 →
        p * (s * x * s) = s * x * s * p) → p * s = 0 ∨ p * s = s) :
    ¬ HasCoequalizers (PureCat (WStarCPSU.{u}ᵒᵖ)) := by
  intro hcoeq
  have := hcoeq
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hr : IsStarProjection (1 - p) := hp.one_sub
  have hrr : (1 - p) * (1 - p) = 1 - p := hr.isIdempotentElem.eq
  set σ : X.unop.base.carrier := p + p - 1 with hσdef
  have hσs : star σ = σ := by
    rw [hσdef, star_sub, star_add, hps, star_one]
  have hσσ : σ * σ = 1 := by
    have h : σ * σ = (p * p + p * p + p * p + p * p) - (p + p + p + p) + 1 := by
      rw [hσdef]; noncomm_ring
    rw [h, hpp]; abel
  have hσp : σ * p = p := by
    have h : σ * p = p * p + p * p - p := by rw [hσdef]; noncomm_ring
    rw [h, hpp]; abel
  have hpσ : p * σ = p := by
    have h : p * σ = p * p + p * p - p := by rw [hσdef]; noncomm_ring
    rw [h, hpp]; abel
  have hσr : σ * (1 - p) = -(1 - p) := by
    have h : σ * (1 - p) = σ - σ * p := by noncomm_ring
    rw [h, hσp, hσdef]; abel
  have hrσ : (1 - p) * σ = -(1 - p) := by
    have h : (1 - p) * σ = σ - p * σ := by noncomm_ring
    rw [h, hpσ, hσdef]; abel
  -- `ad_σ` is an involution, hence an isomorphism, hence pure
  obtain ⟨adσ, hadσ0⟩ := su_exists_ad' (X := X) (w := σ) (le_of_eq (by rw [hσs, hσσ]))
  have hadσ : ∀ x, adσ.unop.toNCPMap x = σ * x * σ := by
    intro x; rw [hadσ0, hσs]
  have hadσ2 : adσ ≫ adσ = 𝟙 X := by
    refine suop_hom_ext fun x => ?_
    have h : σ * (σ * x * σ) * σ = σ * σ * x * (σ * σ) := by noncomm_ring
    rw [suop_comp_apply, hadσ, hadσ, h, hσσ, one_mul, mul_one, suop_id_apply]
  haveI : IsIso adσ := ⟨adσ, hadσ2, hadσ2⟩
  have hpureσ : IsPure adσ :=
    ⟨X, adσ, 𝟙 X, 0, 1, quotient_basics_3 adσ, compr_basics_3 (𝟙 X),
      (Category.comp_id _).symm⟩
  -- the parallel pair in `Pure (vNᵒᵖ)`, and its coequalizer `c`
  set XP : PureCat (WStarCPSU.{u}ᵒᵖ) := PureCat.of X with hXP
  set fσ : XP ⟶ XP := ⟨adσ, hpureσ⟩ with hfσ
  set E := coequalizer (𝟙 XP) fσ with hE
  set c : XP ⟶ E := coequalizer.π (𝟙 XP) fσ with hc
  set e : X ⟶ E.base := c.1 with he
  have hepure : IsPure e := c.2
  have hcond : e = adσ ≫ e := by
    have h : c = fσ ≫ c :=
      (Category.id_comp c).symm.trans (coequalizer.condition (𝟙 XP) fσ)
    exact congrArg (fun k : XP ⟶ E => k.1) h
  have hcommσ : ∀ y : E.base.unop.base.carrier,
      σ * e.unop.toNCPMap y * σ = e.unop.toNCPMap y := by
    intro y
    have h : (adσ ≫ e).unop.toNCPMap y = e.unop.toNCPMap y :=
      congrArg (fun k : X ⟶ E.base => k.unop.toNCPMap y) hcond.symm
    rw [suop_comp_apply, hadσ] at h
    exact h
  have hσ1 : σ + 1 = (2 : ℂ) • p := by rw [hσdef, two_smul]; abel
  have hcommp : ∀ b : X.unop.base.carrier, σ * b * σ = b → p * b = b * p := by
    intro b hb
    have hbσ : σ * b = b * σ := by
      have h : σ * (σ * b * σ) = σ * b := congrArg (fun z => σ * z) hb
      rw [← mul_assoc, ← mul_assoc, hσσ, one_mul] at h
      exact h.symm
    have h1 : (σ + 1) * b = b * (σ + 1) := by
      rw [add_mul, mul_add, hbσ, one_mul, mul_one]
    rw [hσ1] at h1
    have h2 : (2 : ℂ) • (p * b) = (2 : ℂ) • (b * p) := by
      rw [← smul_mul_assoc, ← mul_smul_comm]; exact h1
    have h3 := congrArg (fun z : X.unop.base.carrier => (2 : ℂ)⁻¹ • z) h2
    simpa [smul_smul] using h3
  -- `a = e(1)`, and `p` commutes with `√a x √a` for every effect `x`
  set a : X.unop.base.carrier := e.unop.toNCPMap 1 with ha
  have ha0 : 0 ≤ a := by
    have h := ncpsu_mono e.unop (zero_le_one (α := E.base.unop.base.carrier))
    rwa [ncp_zero_apply] at h
  have ha1 : a ≤ 1 := e.unop.subunital'
  have hasa : star a = a := (IsSelfAdjoint.of_nonneg ha0).star_eq
  set s : X.unop.base.carrier := CFC.sqrt a with hsdef
  have hs0 : (0 : X.unop.base.carrier) ≤ s := CFC.sqrt_nonneg a
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha0
  have hconj : ∀ x : X.unop.base.carrier, 0 ≤ x → x ≤ 1 →
      p * (s * x * s) = s * x * s * p := by
    intro x hx0 hx1
    obtain ⟨z, hz⟩ := su_pure_range hepure hx0 hx1
    rw [← ha, ← hsdef] at hz
    rw [← hz]
    exact hcommp _ (hcommσ z)
  have hdich : p * a = 0 ∨ p * a = a := by
    rcases hcore s hs0 hconj with h | h
    · left; rw [← hss, ← mul_assoc, h, zero_mul]
    · right; rw [← hss, ← mul_assoc, h, hss]
  -- `ad_p` and `ad_{1−p}` are fixed by `ad_σ`, hence factor through `e`
  have hfac : ∀ (w : X.unop.base.carrier) (hw : IsStarProjection w)
      (k : X ⟶ X), IsPure k → (∀ x, k.unop.toNCPMap x = w * x * w) →
      adσ ≫ k = k → w ≤ a := by
    intro w hw k hkp hkval hkσ
    set kP : XP ⟶ XP := ⟨k, hkp⟩ with hkP
    have hcond2 : 𝟙 XP ≫ kP = fσ ≫ kP := by
      refine Subtype.ext ?_
      show 𝟙 X ≫ k = adσ ≫ k
      rw [Category.id_comp, hkσ]
    set d : E ⟶ XP := coequalizer.desc kP hcond2 with hd
    have hcd : c ≫ d = kP := coequalizer.π_desc kP hcond2
    have hcd' : e ≫ d.1 = k := congrArg (fun m : XP ⟶ XP => m.1) hcd
    have h1 : e.unop.toNCPMap (d.1.unop.toNCPMap 1) = w := by
      have h := congrArg
        (fun m : X ⟶ X => m.unop.toNCPMap (1 : X.unop.base.carrier)) hcd'
      simp only [suop_comp_apply] at h
      rw [h, hkval, mul_one, hw.isIdempotentElem.eq]
    have h2 : e.unop.toNCPMap (d.1.unop.toNCPMap 1) ≤ a :=
      ncpsu_mono e.unop d.1.unop.subunital'
    rwa [h1] at h2
  obtain ⟨adp, hadp⟩ := su_exists_ad (X := X) hp.nonneg (by rw [hpp]; exact hp.le_one)
  have hsqrtp : CFC.sqrt p = p := CFC.sqrt_unique hpp hp.nonneg
  have hpurep : IsPure adp :=
    su_isPure_ad_sqrt adp hp.nonneg hp.le_one (by intro x; rw [hadp, hsqrtp])
  have hpleq : p ≤ a := by
    refine hfac p hp adp hpurep hadp (suop_hom_ext fun x => ?_)
    rw [suop_comp_apply, hadσ, hadp]
    have h : σ * (p * x * p) * σ = σ * p * x * (p * σ) := by noncomm_ring
    rw [h, hσp, hpσ]
  obtain ⟨adr, hadr⟩ := su_exists_ad (X := X) hr.nonneg (by rw [hrr]; exact hr.le_one)
  have hsqrtr : CFC.sqrt (1 - p) = 1 - p := CFC.sqrt_unique hrr hr.nonneg
  have hpurer : IsPure adr :=
    su_isPure_ad_sqrt adr hr.nonneg hr.le_one (by intro x; rw [hadr, hsqrtr])
  have hrleq : (1 - p) ≤ a := by
    refine hfac (1 - p) hr adr hpurer hadr (suop_hom_ext fun x => ?_)
    rw [suop_comp_apply, hadσ, hadr]
    have h : σ * ((1 - p) * x * (1 - p)) * σ = σ * (1 - p) * x * ((1 - p) * σ) := by
      noncomm_ring
    rw [h, hσr, hrσ]
    noncomm_ring
  -- the contradiction
  rcases hdich with h | h
  · -- `p a = 0`, so `a ≤ 1 − p`, so `p ≤ 1 − p`, so `p = 0`
    have hap : a * p = 0 := by
      have h' := congrArg star h
      rwa [star_mul, hps, hasa, star_zero] at h'
    have hconj2 : (1 - p) * a * (1 - p) = a := by
      have h1 : (1 - p) * a * (1 - p) = a - p * a - a * p + p * a * p := by
        noncomm_ring
      rw [h1, h, hap]
      simp
    have h2 : (1 - p) * a * (1 - p) ≤ (1 - p) * 1 * (1 - p) :=
      hr.isSelfAdjoint.conjugate_le_conjugate ha1
    rw [hconj2, mul_one, hrr] at h2
    exact hp0 (su_proj_eq_zero hp (hpleq.trans h2)
      (by rw [mul_sub, mul_one, hpp, sub_self]))
  · -- `p a = a`, so `a ≤ p`, so `1 − p ≤ p`, so `p = 1`
    have hap : a * p = a := by
      have h' := congrArg star h
      rwa [star_mul, hps, hasa] at h'
    have hconj2 : p * a * p = a := by rw [h, hap]
    have h2 : p * a * p ≤ p * 1 * p := hp.isSelfAdjoint.conjugate_le_conjugate ha1
    rw [hconj2, mul_one, hpp] at h2
    have hz : (1 : X.unop.base.carrier) - p = 0 :=
      su_proj_eq_zero hr (hrleq.trans h2) (by rw [sub_mul, one_mul, hpp, sub_self])
    exact hp1 (sub_eq_zero.mp hz).symm

/-- The two-dimensional Hilbert space `ℂ²`, in `Type u`. -/
private abbrev Hu : Type u := EuclideanSpace ℂ (ULift.{u} (Fin 2))

/-- `B(ℂ²)` as an object of `vN_cpsuᵒᵖ`. -/
private noncomputable abbrev bhObj : WStarCPSU.{u}ᵒᵖ :=
  Opposite.op (WStarCPSU.of (WStar.of (Hu.{u} →L[ℂ] Hu.{u})))

/-- **224VII at `vNᵒᵖ`** (`exc-purec-equal`, eff.tex:7218, Exercise\*;
solution bsols.tex:3480): `Pure (vNᵒᵖ)` does **not** have all coequalizers —
already `id` and `ad_σ` on `B(ℂ²)`, for the symmetry `σ = 2p − 1` of a
rank-one projection `p`, have none. -/
theorem su_exc_purec_equal : ¬ HasCoequalizers (PureCat (WStarCPSU.{u}ᵒᵖ)) := by
  set ξ₀ : Hu.{u} := EuclideanSpace.single (ULift.up 0) (1 : ℂ) with hξ₀
  set ξ₁ : Hu.{u} := EuclideanSpace.single (ULift.up 1) (1 : ℂ) with hξ₁
  have hn₀ : ‖ξ₀‖ = 1 := by simp [hξ₀]
  have hn₁ : ‖ξ₁‖ = 1 := by simp [hξ₁]
  have hproj : IsStarProjection (rk1 ξ₀) := rk1_isStarProjection hn₀
  have h₀ne : ξ₀ ≠ 0 := by
    intro h; rw [h] at hn₀; simp at hn₀
  have h₁ne : ξ₁ ≠ 0 := by
    intro h; rw [h] at hn₁; simp at hn₁
  refine su_no_coequalizer_of_proj (X := bhObj.{u}) (p := rk1 ξ₀) hproj ?_ ?_ ?_
  · intro h
    have h1 : rk1 ξ₀ ξ₀ = ξ₀ := by
      rw [rk1_apply, inner_self_eq_norm_sq_to_K, hn₀]
      simp
    rw [h] at h1
    exact h₀ne h1.symm
  · intro h
    have h1 : rk1 ξ₀ ξ₁ = 0 := by
      rw [rk1_apply]
      have hz : (⟪ξ₀, ξ₁⟫ : ℂ) = 0 := by
        simp [hξ₀, hξ₁, EuclideanSpace.inner_single_left]
      rw [hz, zero_smul]
    rw [h] at h1
    exact h₁ne h1
  · intro s hs0 hcomm
    exact proj_mul_selfAdjoint (IsSelfAdjoint.of_nonneg hs0) hproj hcomm

/-! ### `Pure (vNᵒᵖ)` has no binary coproducts (224VI)

`bsols.tex`:3358 classifies the non-zero pure maps `𝒜 → ℂ` by a GNS
representation (using `paschke-pure` and the factoriality of `⌈⌈p⌉⌉𝒜` for a
minimal projection `p`), identifies `𝒜` with `M₂`, and then contradicts the
universal property with the two coordinate maps of `ℂ²`.  **That is the
route taken**: the opening task is `su_pure_state_classification`, the rest
is `su_224VI_printed`, and `su_exc_purec_no_biproduct` is the latter.

A shorter argument, which needs none of that machinery, is kept alongside
as `su_exc_purec_no_biproduct_short`: write `π₁, π₂ : 𝒜 → ℂ` for the two
coprojections of a hypothetical coproduct, `a₀ = ĝ₀(1)` for the value of
the mediating map of `(id, id)` and `a₁ = ĝ₁(1)` for that of `(id, 0)`, so
that `π₁(a₀) = π₂(a₀) = 1`, `π₁(a₁) = 1` and `π₂(a₁) = 0`.  Then both `π_i`
are **states** fixing `a₀`, so `π_i(√a₀ a₁ √a₀) = π_i(a₁)` by
`su_state_sqrtConj`; while `√a₀ a₁ √a₀` lies in the range of `ĝ₀` by
`su_pure_range`, on which `π₁` and `π₂` agree — both being inverse to
`ĝ₀`.  Hence `1 = π₁(a₁) = π₂(a₁) = 0`. -/

/-! #### The printed route's first task: the pure maps `𝒜 → ℂ`

The exercise's opening task — "first show that for any non-zero pure map
`f : 𝒜 → ℂ` there are a Hilbert space `ℋ`, an `x ∈ ℋ`, a von Neumann
algebra `𝒞` and an isomorphism `φ : B(ℋ) ⊕ 𝒞 → 𝒜` with
`f(φ(T,c)) = ⟪x, T x⟫`" — is bsols.tex:3357-3387, and it *is* formalized
here, as `su_pure_state_iso` (algebra level) and
`su_pure_state_classification` (at the morphisms of `vNᵒᵖ`).  Three of the
solution's four steps are transcribed; the fourth is replaced, and the
replacement is named at `su_pure_state_iso`.

1. *(bsols.tex:3361-3368)* `f = c ∘ h` for a filter `c` and a corner `h`;
   `c` is injective (**169XII** `dils_filters_injective`), so the
   intermediate algebra is one-dimensional, so `h` is `f/f(1)` times the
   standard corner of `p = ⌊a⌋` and `p𝒜p = ℂp` — `p` is a **minimal
   projection** (`su_pure_state_minimal`, with `su_corner_iso` for
   **169IV**).  The print asserts the intermediate algebra is `ℂ` without
   argument; injectivity of the filter is what supplies it.
2. *(bsols.tex:3370-3375)* the GNS representation `ϱ` of `f` is surjective
   by **171VII** `paschke_pure` (`su_pure_state_rep`).  A GNS
   representation of a state *is* a minimal Stinespring dilation of it read
   as a map into `B(H₁)` for a one-dimensional `H₁`; **140III**
   `stinespring_is_paschke` makes that a Paschke dilation, so `paschke_pure`
   applies to it verbatim.  The one-dimensional bridge — `ℂᵤ ≅ B(H₁)` as
   ncp-maps, hence `z ↦ z·1` is a filter — is `suScalarEmbed`,
   `suScalarNCP` and `su_isFilterFor_suScalarEmbed`.
3. *(bsols.tex:3376-3379)* **the one divergence.**  The print gets `ϱ`
   *injective* from the factoriality of `⌈⌈p⌉⌉𝒜`
   (`Theses.A.VN.IsMinimalProjection.isFactor_cceil`, built for this row).
   Here `ϱ` is not restricted to `⌈⌈p⌉⌉𝒜` first: **69IV** `carrier_miu`
   gives a central projection `⌈ϱ⌉` with `ϱ a = ϱ b ↔ ⌈ϱ⌉a = ⌈ϱ⌉b`, which
   is the same conclusion — `ϱ` separates `⌈ϱ⌉𝒜` — without the detour
   through minimality.  Step 1 is therefore not *used* by steps 2-4; it is
   kept because the print states it and because stages (3)-(5) of the
   solution need it (they classify `⌈π₁ ∘ φ⌉`).
4. *(bsols.tex:3380-3387)* `𝒜 ≅ B(ℋ) ⊕ 𝒞` and `f = ⟪x, (·) x⟫` on the
   first summand (`su_pure_state_iso`), with `𝒞 = ⌈ϱ⌉^⊥𝒜` the corner of
   **67IV**.

What the printed solution does after this — its stages (2)-(5) — is the
section below, ending in `su_224VI_printed`. -/

section PureStateClassification

set_option linter.unusedSectionVars false

/-- **169IV** together with the uniqueness half of **169II**: a corner `h`
for `a` is the standard corner `h_{⌊a⌋}` followed by an ncp-isomorphism `v`.

This is `Theses.B.Dils.pext_corner_iso`, which is `private` in
`B/Dils/Pure.lean`; the proof is that one, unchanged. -/
theorem su_corner_iso {P C : Type u} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [Theses.VonNeumannAlgebra P] [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (h : Theses.NCPMap P C) (a : P)
    (hc : Theses.B.Dils.IsCornerFor h a) :
    ∃ (hp : Theses.NCPMap P (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a)))
      (v : Theses.NCPMap (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a)) C)
      (u : Theses.NCPMap C (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a))),
      (∀ b : P, (hp b).1 = Theses.A.VN.floor a * b * Theses.A.VN.floor a) ∧
      (∀ x : P, v (hp x) = h x) ∧
      (∀ y : C, v (u y) = y) ∧
      ∀ z : Theses.B.Dils.cornerSet P (Theses.A.VN.floor a), u (v z) = z := by
  obtain ⟨hp, hval, hpc⟩ := Theses.B.Dils.standard_corner_dils a hc.1
  obtain ⟨v, hv, -⟩ :=
    hpc.2.2 C inferInstance inferInstance inferInstance h hc.2.1
  obtain ⟨u, hu, -⟩ :=
    hc.2.2 (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a)) inferInstance
      inferInstance inferInstance hp hpc.2.1
  refine ⟨hp, v, u, hval, hv, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := Theses.A.Proc.exists_ncpComp v u
    obtain ⟨idm, hidm⟩ := Theses.A.Proc.exists_ncpId C
    obtain ⟨w₀, -, huniq⟩ :=
      hc.2.2 C inferInstance inferInstance inferInstance h hc.2.1
    have h1 : w = idm := (huniq w fun x => by rw [hw, hu, hv]).trans
      (huniq idm fun x => by rw [hidm]).symm
    intro y
    have h2 := DFunLike.congr_fun h1 y
    rw [hw, hidm] at h2
    exact h2
  · obtain ⟨w, hw⟩ := Theses.A.Proc.exists_ncpComp u v
    obtain ⟨idm, hidm⟩ :=
      Theses.A.Proc.exists_ncpId (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a))
    obtain ⟨w₀, -, huniq⟩ :=
      hpc.2.2 (Theses.B.Dils.cornerSet P (Theses.A.VN.floor a)) inferInstance
        inferInstance inferInstance hp hpc.2.1
    have h1 : w = idm := (huniq w fun x => by rw [hw, hv, hu]).trans
      (huniq idm fun x => by rw [hidm]).symm
    intro z
    have h2 := DFunLike.congr_fun h1 z
    rw [hw, hidm] at h2
    exact h2

/-- An ncp-map into the scalars takes real values at self-adjoint
elements. -/
theorem su_ncp_scalar_real {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (f : Theses.NCPMap A (ULift.{u, 0} ℂ)) {x : A}
    (hx : IsSelfAdjoint x) :
    (((f x : ULift.{u, 0} ℂ).down.re : ℝ) : ℂ) = (f x : ULift.{u, 0} ℂ).down := by
  have h : (f (star x) : ULift.{u, 0} ℂ) = star (f x) := Theses.A.VN.ncp_star f x
  rw [hx.star_eq] at h
  have h2 : star ((f x : ULift.{u, 0} ℂ).down) = (f x : ULift.{u, 0} ℂ).down := by
    rw [← Theses.B.Dils.CU.down_star, ← h]
  exact Complex.conj_eq_iff_re.mp (by rw [← Complex.star_def]; exact h2)

/-- **bsols.tex:3361-3368**, the solution's first step: a pure map
`f : 𝒜 → ℂ` with `f(1) ≠ 0` is `f(1)` times the standard corner of a
**minimal** projection `p`, i.e. `f(a)·p = f(1)·pap`.

`f = c ∘ h` with `c` a filter and `h` a corner; `c` is injective
(**169XII** `dils_filters_injective`), so every element of the intermediate
algebra is a scalar multiple of `h(1)` — the print's "`c : ℂ → ℂ` is
`c(1)·id`", which it assumes rather than argues.  `su_corner_iso` then
identifies the corner with the standard corner of `p = ⌊a⌋`, and the
resulting `p𝒜p = ℂp` is `p` minimal by
`Theses.A.VN.isMinimalProjection_of_corner_scalar`. -/
theorem su_pure_state_minimal {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A]
    (f : Theses.NCPMap A (ULift.{u, 0} ℂ)) (hpure : Theses.B.Dils.IsPureMap f)
    (hf1 : (f 1 : ULift.{u, 0} ℂ) ≠ 0) :
    ∃ p : A, Theses.A.VN.IsMinimalProjection p ∧
      ∀ a : A, (f a : ULift.{u, 0} ℂ).down • p
        = (f 1 : ULift.{u, 0} ℂ).down • (p * a * p) := by
  obtain ⟨C, iC, iP, iS, h, c, hcorner, hfilter, hcomp⟩ := hpure
  let _ := iC; let _ := iP; let _ := iS
  have hcinj : Function.Injective ⇑c := Theses.B.Dils.dils_filters_injective c hfilter
  obtain ⟨a₀, hca₀⟩ := hcorner
  obtain ⟨hp, v, u, hval, hvhp, hvu, huv⟩ := su_corner_iso h a₀ hca₀
  have hproj : IsStarProjection (Theses.A.VN.floor a₀) :=
    (inferInstance : Fact (IsStarProjection (Theses.A.VN.floor a₀))).out
  set p : A := Theses.A.VN.floor a₀ with hpdef
  have : Fact (IsStarProjection p) := by rw [hpdef]; infer_instance
  set e : C := h 1 with hedef
  have hce : (c e : ULift.{u, 0} ℂ) = f 1 := (hcomp 1).symm
  have hf1d : (f 1 : ULift.{u, 0} ℂ).down ≠ 0 := fun hz =>
    hf1 (Theses.B.Dils.CU.down_injective (by rw [hz]; rfl))
  have hce0' : (c e : ULift.{u, 0} ℂ).down ≠ 0 := by rw [hce]; exact hf1d
  -- every element of the intermediate algebra is a scalar multiple of `e`
  have hspan : ∀ y : C,
      y = ((c y : ULift.{u, 0} ℂ).down / (c e : ULift.{u, 0} ℂ).down) • e := by
    intro y
    refine hcinj ?_
    rw [ncp_smul_apply]
    refine (Theses.B.Dils.CU.down_injective ?_).symm
    rw [Theses.B.Dils.CU.down_smul]
    exact div_mul_cancel₀ _ hce0'
  have hhp1 : (hp 1 : Theses.B.Dils.cornerSet A p).1 = p := by
    rw [hval 1, mul_one, hproj.isIdempotentElem.eq]
  have hue : u e = hp 1 := by rw [hedef, ← hvhp 1, huv]
  have hmaster : ∀ x : A, (hp x : Theses.B.Dils.cornerSet A p) =
      ((f x : ULift.{u, 0} ℂ).down / (f 1 : ULift.{u, 0} ℂ).down) • hp 1 := by
    intro x
    have h1 : (hp x : Theses.B.Dils.cornerSet A p) = u (h x) := by rw [← hvhp x, huv]
    have h3 : (c (h x) : ULift.{u, 0} ℂ) = f x := (hcomp x).symm
    rw [h1, hspan (h x), h3, hce, ncp_smul_apply, hue]
  have hpxp : ∀ x : A, p * x * p
      = ((f x : ULift.{u, 0} ℂ).down / (f 1 : ULift.{u, 0} ℂ).down) • p := by
    intro x
    have h := congrArg (Subtype.val : Theses.B.Dils.cornerSet A p → A) (hmaster x)
    rw [hval x] at h
    rw [h]
    show ((f x : ULift.{u, 0} ℂ).down / (f 1 : ULift.{u, 0} ℂ).down)
      • (hp 1 : Theses.B.Dils.cornerSet A p).1 = _
    rw [hhp1]
  -- `p ≠ 0`: otherwise `h(1) = v(h_p(1)) = 0` and `f(1) = c(h(1)) = 0`
  have hp0 : p ≠ 0 := by
    intro hz
    refine hf1 ?_
    have h1 : (hp 1 : Theses.B.Dils.cornerSet A p) = 0 :=
      Subtype.ext (by rw [hhp1, hz]; rfl)
    have h2 : e = 0 := by rw [hedef, ← hvhp 1, h1, ncp_zero_apply]
    rw [← hce, h2, ncp_zero_apply]
  refine ⟨p, Theses.A.VN.isMinimalProjection_of_corner_scalar hproj hp0 ?_, fun a => ?_⟩
  · intro x hx hxp
    refine ⟨(f x : ULift.{u, 0} ℂ).down.re / (f 1 : ULift.{u, 0} ℂ).down.re, ?_⟩
    have hr : (((f x : ULift.{u, 0} ℂ).down.re
          / (f 1 : ULift.{u, 0} ℂ).down.re : ℝ) : ℂ)
        = (f x : ULift.{u, 0} ℂ).down / (f 1 : ULift.{u, 0} ℂ).down := by
      rw [Complex.ofReal_div, su_ncp_scalar_real f hx,
        su_ncp_scalar_real f (IsSelfAdjoint.one A)]
    rw [hr, ← hpxp x, hxp]
  · rw [hpxp a, smul_smul]
    congr 1
    field_simp

/-! ##### `ℂᵤ ≅ B(H₁)`, `H₁` one-dimensional

**140III** `stinespring_is_paschke` wants a map into `B(ℋ)`, and the state
`f` maps into `ℂᵤ`.  A one-dimensional `ℋ` bridges the two: `z ↦ z·1` and
`T ↦ ⟪e₁, T e₁⟫` are mutually inverse ncp-maps, so the first is a *filter*
(`isFilterFor_of_ncpIso` off `isFilterFor_ncpId`), and post-composing with
it keeps a pure map pure. -/

/-- A one-dimensional Hilbert space in universe `u`. -/
private abbrev suH1 : Type u := EuclideanSpace ℂ (ULift.{u} (Fin 1))

/-- Its unit vector. -/
private noncomputable def suE1 : suH1.{u} := EuclideanSpace.single (ULift.up 0) (1 : ℂ)

private theorem su_inner_e1 (x : suH1.{u}) : (⟪suE1.{u}, x⟫ : ℂ) = x (ULift.up 0) := by
  rw [suE1, EuclideanSpace.inner_single_left]
  simp

private theorem su_inner_e1_self : (⟪suE1.{u}, suE1.{u}⟫ : ℂ) = 1 := by
  rw [su_inner_e1]
  simp [suE1]

private theorem suH1_eq_smul (x : suH1.{u}) : x = (⟪suE1.{u}, x⟫ : ℂ) • suE1.{u} := by
  ext i
  have hi : i = ULift.up (0 : Fin 1) := Subsingleton.elim _ _
  subst hi
  rw [su_inner_e1]
  simp [suE1]

private theorem suH1_op_eq_smul (T : suH1.{u} →L[ℂ] suH1.{u}) :
    T = (⟪suE1.{u}, T suE1.{u}⟫ : ℂ) • 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  calc T x = T ((⟪suE1.{u}, x⟫ : ℂ) • suE1.{u}) := by rw [← suH1_eq_smul x]
    _ = (⟪suE1.{u}, x⟫ : ℂ) • T suE1.{u} := by rw [map_smul]
    _ = (⟪suE1.{u}, x⟫ : ℂ) • ((⟪suE1.{u}, T suE1.{u}⟫ : ℂ) • suE1.{u}) := by
        conv_lhs => rw [suH1_eq_smul (T suE1.{u})]
    _ = (⟪suE1.{u}, T suE1.{u}⟫ : ℂ) • ((⟪suE1.{u}, x⟫ : ℂ) • suE1.{u}) := by
        rw [smul_smul, smul_smul, mul_comm]
    _ = (⟪suE1.{u}, T suE1.{u}⟫ : ℂ) • x := by rw [← suH1_eq_smul x]
    _ = ((⟪suE1.{u}, T suE1.{u}⟫ : ℂ) • (1 : suH1.{u} →L[ℂ] suH1.{u})) x := rfl

/-- `T ↦ ⟪e₁, T e₁⟫ : B(H₁) → ℂᵤ`, the vector state at `e₁`. -/
private noncomputable def suScalarNCP :
    Theses.NCPMap (suH1.{u} →L[ℂ] suH1.{u}) (ULift.{u} ℂ) :=
  npNCP (Theses.A.VN.vectorNP suE1.{u})

private theorem suScalarNCP_apply (T : suH1.{u} →L[ℂ] suH1.{u}) :
    suScalarNCP T = ULift.up (⟪suE1.{u}, T suE1.{u}⟫ : ℂ) := rfl

/-- `z ↦ z·1 : ℂᵤ → B(H₁)`. -/
private noncomputable def suScalarEmbed :
    Theses.NCPMap (ULift.{u} ℂ) (suH1.{u} →L[ℂ] suH1.{u}) :=
  Theses.A.VN.ncpOfNonneg (zero_le_one : (0 : suH1.{u} →L[ℂ] suH1.{u}) ≤ 1)

private theorem suScalarEmbed_apply (z : ULift.{u} ℂ) :
    suScalarEmbed z = z.down • (1 : suH1.{u} →L[ℂ] suH1.{u}) := rfl

private theorem suScalarNCP_suScalarEmbed (z : ULift.{u} ℂ) :
    suScalarNCP (suScalarEmbed.{u} z) = z := by
  refine ULift.ext _ _ ?_
  rw [suScalarNCP_apply, suScalarEmbed_apply]
  show (⟪suE1.{u}, (z.down • (1 : suH1.{u} →L[ℂ] suH1.{u})) suE1.{u}⟫ : ℂ) = z.down
  rw [show ((z.down • (1 : suH1.{u} →L[ℂ] suH1.{u})) suE1.{u}) = z.down • suE1.{u}
      from rfl, inner_smul_right, su_inner_e1_self, mul_one]

private theorem suScalarEmbed_suScalarNCP (T : suH1.{u} →L[ℂ] suH1.{u}) :
    suScalarEmbed.{u} (suScalarNCP T) = T := by
  rw [suScalarEmbed_apply, suScalarNCP_apply]
  exact (suH1_op_eq_smul T).symm

private theorem suScalarEmbed_one :
    (suScalarEmbed.{u} 1 : suH1.{u} →L[ℂ] suH1.{u}) = 1 := by
  rw [suScalarEmbed_apply]
  show (1 : ℂ) • (1 : suH1.{u} →L[ℂ] suH1.{u}) = 1
  rw [one_smul]

/-- The scalar embedding is a **filter** for `1`: it is an ncp-isomorphism,
and the identity is a filter for `1` (**169VIII**). -/
private theorem su_isFilter_suScalarEmbed :
    Theses.B.Dils.IsFilter suScalarEmbed.{u} :=
  ⟨1, Theses.B.Dils.isFilterFor_of_ncpIso
    (d := Theses.B.Dils.ncpId (suH1.{u} →L[ℂ] suH1.{u}))
    Theses.B.Dils.isFilterFor_ncpId suScalarEmbed.{u} suScalarNCP.{u}
    (fun _ => rfl) suScalarEmbed_one
    suScalarNCP_suScalarEmbed suScalarEmbed_suScalarNCP⟩

/-! ##### The classification itself -/

/-- **bsols.tex:3370-3379**: a pure map `f : 𝒜 → ℂ` is the vector state of
a **surjective** normal representation `ϱ` of `𝒜` on a Hilbert space.

This is the print's "let `ϱ` be a GNS representation of `f`; `f` is pure, so
by **171VII** `paschke-pure` `ϱ` is surjective".  A GNS representation of a
state is a *minimal Stinespring dilation* of it, once `f` is read as a map
into `B(H₁)` for a one-dimensional `H₁` — which keeps it pure, the scalar
embedding being a filter (`su_isFilter_suScalarEmbed`).  **140III**
`stinespring_is_paschke` turns that dilation into a Paschke dilation, and
`paschke_pure` applies to it unchanged. -/
theorem su_pure_state_rep {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A]
    (f : Theses.NCPMap A (ULift.{u, 0} ℂ)) (hf : Theses.B.Dils.IsPureMap f) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (ρ : Theses.NMIUMap A (K →L[ℂ] K)) (y : K),
      Function.Surjective ⇑ρ ∧ ∀ a : A, (f a).down = (⟪y, ρ a y⟫ : ℂ) := by
  obtain ⟨φ, hφ⟩ := Theses.A.Proc.exists_ncpComp suScalarEmbed.{u} f
  have hφpure : Theses.B.Dils.IsPureMap φ :=
    Theses.B.Dils.isPureMap_ncpComp (su_procIsPure_of_isPureMap hf)
      (Theses.A.Proc.IsPure.filter
        (Theses.B.Dils.procIsFilter_of_isFilterFor
          su_isFilter_suScalarEmbed.choose_spec)) φ hφ
  obtain ⟨D, hmin⟩ := Theses.B.Dils.exists_minimal_stinespringDilation φ
  obtain ⟨vnK, hh, -, hpasch⟩ := Theses.B.Dils.stinespring_is_paschke φ D hmin
  have hsurj : Function.Surjective ⇑D.ρ :=
    (Theses.B.Dils.paschke_pure φ ⟨D.K →L[ℂ] D.K, vnK, D.ρ, hh⟩ hpasch).mp hφpure
  refine ⟨D.K, inferInstance, inferInstance, inferInstance, D.ρ, D.V suE1.{u},
    hsurj, fun a => ?_⟩
  have hval : (φ a : suH1.{u} →L[ℂ] suH1.{u}) = (f a).down • 1 := by
    rw [hφ, suScalarEmbed_apply]
  have hD := D.eq a
  rw [hval] at hD
  have hcong :=
    congrArg (fun T : suH1.{u} →L[ℂ] suH1.{u} => (⟪suE1.{u}, T suE1.{u}⟫ : ℂ)) hD
  rw [show (((f a).down • (1 : suH1.{u} →L[ℂ] suH1.{u})) suE1.{u})
      = (f a).down • suE1.{u} from rfl, inner_smul_right, su_inner_e1_self,
    mul_one] at hcong
  rw [hcong]
  show (⟪suE1.{u},
    (ContinuousLinearMap.adjoint D.V).comp ((D.ρ a).comp D.V) suE1.{u}⟫ : ℂ) = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- **bsols.tex:3380-3387**, the exercise's first task: a pure map
`f : 𝒜 → ℂ` comes with a Hilbert space `K`, a von Neumann algebra `𝒞` and
an nmiu-**isomorphism** `Φ : 𝒜 → B(K) ⊕ 𝒞` — the inverse of the printed
`φ` — for which `f` is the vector state of `y ∈ K` on the first summand.

The central projection is `⌈ϱ⌉` (**69IV** `carrier_miu`): `ϱ` is surjective
with kernel `⌈ϱ⌉^⊥𝒜`, so `𝒞 = ⌈ϱ⌉^⊥𝒜` (**67IV**'s corner, a von Neumann
algebra in its own right) and `a ↦ (ϱ a, ⌈ϱ⌉^⊥a)` is the isomorphism.

*Divergence.*  The print restricts `f` to `⌈⌈p⌉⌉𝒜` first and gets the
injectivity of `ϱ` from the factoriality of that corner
(`Theses.A.VN.IsMinimalProjection.isFactor_cceil`).  Here nothing is
restricted: `carrier_miu` says outright that `ϱ` separates `⌈ϱ⌉𝒜`, which is
the same conclusion.  So `su_pure_state_minimal` — the print's step that
produces `p` — is not used by this proof, and the print's `𝒞` (`𝒜` minus
the central carrier of `p`) is here `⌈ϱ⌉^⊥𝒜`; the two agree, since
`⌈ϱ⌉ = ⌈⌈p⌉⌉`. -/
theorem su_pure_state_iso {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A]
    (f : Theses.NCPMap A (ULift.{u, 0} ℂ)) (hf : Theses.B.Dils.IsPureMap f) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (_ : Theses.VonNeumannAlgebra C)
      (Φ : Theses.NMIUMap A ((K →L[ℂ] K) × C)) (y : K),
      Function.Bijective ⇑Φ ∧ ∀ a : A, (f a).down = (⟪y, (Φ a).1 y⟫ : ℂ) := by
  obtain ⟨K, iN, iI, iC, ρ, y, hsurj, hfval⟩ := su_pure_state_rep f hf
  obtain ⟨z, hzproj, hzcen, hker⟩ : ∃ z : A, IsStarProjection z ∧
      Theses.A.VN.IsCentral A z ∧
      ∀ a b : A, (ρ a : K →L[ℂ] K) = ρ b ↔ z * a = z * b :=
    ⟨Theses.A.VN.carrier (Theses.A.VN.nmiuP ρ) ρ.preservesDirSups',
      (Theses.A.VN.carrier_spec _ _).1,
      (Theses.A.VN.carrier_miu ρ (Theses.A.VN.nmiuP ρ) ρ.preservesDirSups'
        (fun _ => rfl)).1,
      fun a b => (Theses.A.VN.nmiu_factors ρ (Theses.A.VN.nmiuP ρ)
        ρ.preservesDirSups' (fun _ => rfl) a b).2⟩
  set c : Theses.A.VN.CentralProj A := ⟨z, hzproj, hzcen⟩ with hcdef
  set d : Theses.NMIUMap A (c.compl).sub := (c.compl).compress with hddef
  refine ⟨K, iN, iI, iC, (c.compl).sub, inferInstance, inferInstance, inferInstance,
    inferInstance,
    ⟨{ toFun := fun a => (ρ a, d a)
       map_one' := Prod.ext (map_one ρ.toStarAlgHom) (map_one d.toStarAlgHom)
       map_mul' := fun a b => Prod.ext (map_mul ρ.toStarAlgHom a b)
         (map_mul d.toStarAlgHom a b)
       map_zero' := Prod.ext (map_zero ρ.toStarAlgHom) (map_zero d.toStarAlgHom)
       map_add' := fun a b => Prod.ext (map_add ρ.toStarAlgHom a b)
         (map_add d.toStarAlgHom a b)
       commutes' := fun r => Prod.ext (ρ.toStarAlgHom.commutes r)
         (d.toStarAlgHom.commutes r)
       map_star' := fun a => Prod.ext (map_star ρ.toStarAlgHom a)
         (map_star d.toStarAlgHom a) },
      ?_⟩, y, ⟨?_, ?_⟩, fun a => hfval a⟩
  · intro D s hne hdir hlub
    have h1 := ρ.preservesDirSups' D s hne hdir hlub
    have h2 := d.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨h1.1 ⟨e, he, rfl⟩, h2.1 ⟨e, he, rfl⟩⟩
    · rintro ⟨v, w⟩ hvw
      exact ⟨h1.2 (by rintro _ ⟨e, he, rfl⟩; exact (hvw ⟨e, he, rfl⟩).1),
        h2.2 (by rintro _ ⟨e, he, rfl⟩; exact (hvw ⟨e, he, rfl⟩).2)⟩
  · intro a b hab
    have h1 : (ρ a : K →L[ℂ] K) = ρ b := congrArg Prod.fst hab
    have h2 : (1 - z) * a = (1 - z) * b :=
      congrArg (Subtype.val : (c.compl).sub → A) (congrArg Prod.snd hab)
    have h3 := (hker a b).mp h1
    have e₁ : z * a + (1 - z) * a = a := by rw [sub_mul, one_mul]; abel
    have e₂ : z * b + (1 - z) * b = b := by rw [sub_mul, one_mul]; abel
    rw [← e₁, ← e₂, h3, h2]
  · rintro ⟨T, w⟩
    obtain ⟨a, ha⟩ := hsurj T
    have hzw : z * (w : A) = 0 := by
      have hw : (1 - z) * (w : A) = (w : A) := w.2
      rw [← hw, ← mul_assoc, mul_sub, mul_one, hzproj.isIdempotentElem.eq, sub_self,
        zero_mul]
    refine ⟨z * a + (w : A), Prod.ext ?_ ?_⟩
    · show (ρ (z * a + (w : A)) : K →L[ℂ] K) = T
      have hadd : (ρ (z * a + (w : A)) : K →L[ℂ] K) = ρ (z * a) + ρ (w : A) :=
        map_add ρ.toStarAlgHom _ _
      have hw0 : (ρ (w : A) : K →L[ℂ] K) = 0 := by
        have h : (ρ (w : A) : K →L[ℂ] K) = ρ 0 := by
          refine (hker _ _).mpr ?_
          rw [hzw, mul_zero]
        rw [h]
        exact map_zero ρ.toStarAlgHom
      have hza : (ρ (z * a) : K →L[ℂ] K) = ρ a := by
        refine (hker _ _).mpr ?_
        rw [← mul_assoc, hzproj.isIdempotentElem.eq]
      rw [hadd, hw0, hza, ha, add_zero]
    · refine Subtype.ext ?_
      show (1 - z) * (z * a + (w : A)) = (w : A)
      have hw : (1 - z) * (w : A) = (w : A) := w.2
      rw [mul_add, hw, ← mul_assoc, sub_mul, one_mul, hzproj.isIdempotentElem.eq,
        sub_self, zero_mul, zero_add]

/-- **bsols.tex:3357-3387**, the exercise's first task, at the morphisms of
`vNᵒᵖ`: a pure map `ℂ ⟶ 𝒜` of the effectus — an ncp-map `𝒜 → ℂ` — is the
vector state of a direct summand `B(K)` of `𝒜`. -/
theorem su_pure_state_classification {X : WStarCPSU.{u}ᵒᵖ} (f : suI.{u} ⟶ X)
    (hf : IsPure f) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (_ : Theses.VonNeumannAlgebra C)
      (Φ : Theses.NMIUMap X.unop.base.carrier ((K →L[ℂ] K) × C)) (y : K),
      Function.Bijective ⇑Φ ∧
        ∀ a : X.unop.base.carrier,
          (f.unop.toNCPMap a).down = (⟪y, (Φ a).1 y⟫ : ℂ) :=
  su_pure_state_iso f.unop.toNCPMap
    (Theses.B.Dils.isPureMap_of_procIsPure (su_procPure_of_isPure hf))

/-! ##### The dagger of the standard filter of `|z⟩⟨z|` (215VIa.2, 215VII)

The second stage of the printed solution (bsols.tex:3400) writes the
mediating map as `h = φ ∘ p† ∘ c_{|z⟩⟨z|}` after noting that
"`T ↦ ⟪z, T z⟫` is the dagger of the standard filter `c_{|z⟩⟨z|}`".  That is
215VIa.2 at the rank-one projection `|z⟩⟨z|` of `B(ℋ)`, whose corner is the
scalars: the filter is `w ↦ w·|z⟩⟨z| : ℂ → B(ℋ)` and its dagger is the
vector state `T ↦ ⟪z, T z⟫ : B(ℋ) → ℂ`.  It is also the smallest instance
of the nested remark 2150.72, "`φ = ad_T` has `φ† = ad_{T*}`": here
`c = ad_{V*}` and `c† = ad_V` for `V : ℂ → ℋ`, `1 ↦ z`.

Rather than identifying `⌈|z⟩⟨z|⌉B(ℋ)⌈|z⟩⟨z|⌉` with `ℂ`, the pair is fed to
`su_dagger_of_quotient` directly: `c` is pure (it is `ad_{V*}` after the
scalar embedding, which is a filter, `su_isFilter_suScalarEmbed`) and
faithful (`|z⟩⟨z| ≠ 0`), hence a quotient for `|z⟩⟨z|ᵖ`
(`su_isQuotient_of_pure_faithful`), and `c ≫ c† = asrt_{|z⟩⟨z|}` is the
computation `|z⟩⟨z| T |z⟩⟨z| = ⟪z, T z⟫·|z⟩⟨z|`. -/

section KetBra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- `|z⟩⟨z| z = z` for a unit vector `z`. -/
theorem su_rk1_apply_self {z : H} (hz : ‖z‖ = 1) : rk1 z z = z := by
  have hzz : (⟪z, z⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz]
    norm_num
  rw [rk1_apply, hzz, one_smul]

/-- `|z⟩⟨z| ≠ 0` for a unit vector `z`. -/
theorem su_rk1_ne_zero {z : H} (hz : ‖z‖ = 1) : rk1 z ≠ 0 := by
  intro h0
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  refine hz0 ?_
  have h1 : rk1 z z = z := su_rk1_apply_self hz
  rw [h0] at h1
  exact h1.symm

/-- `|z⟩⟨z| T |z⟩⟨z| = ⟪z, T z⟫·|z⟩⟨z|`. -/
theorem su_rk1_conj (z : H) (T : H →L[ℂ] H) :
    rk1 z * T * rk1 z = (⟪z, T z⟫ : ℂ) • rk1 z := by
  refine ContinuousLinearMap.ext fun x => ?_
  show rk1 z (T (rk1 z x)) = ((⟪z, T z⟫ : ℂ) • rk1 z) x
  calc rk1 z (T (rk1 z x)) = rk1 z (T ((⟪z, x⟫ : ℂ) • z)) := by rw [rk1_apply z x]
    _ = rk1 z ((⟪z, x⟫ : ℂ) • T z) := by rw [map_smul]
    _ = (⟪z, (⟪z, x⟫ : ℂ) • T z⟫ : ℂ) • z := rk1_apply z _
    _ = ((⟪z, x⟫ : ℂ) * ⟪z, T z⟫) • z := by rw [inner_smul_right]
    _ = (⟪z, T z⟫ : ℂ) • ((⟪z, x⟫ : ℂ) • z) := by rw [smul_smul, mul_comm]
    _ = ((⟪z, T z⟫ : ℂ) • rk1 z) x := by rw [← rk1_apply z x]; rfl

/-- The standard filter `c : ℂ → B(ℋ)`, `w ↦ w·|z⟩⟨z|`, of a rank-one
projection and the vector state `c† : B(ℋ) → ℂ`, `T ↦ ⟪z, T z⟫`, are maps
`B(ℋ) ⟶ ℂ` and `ℂ ⟶ B(ℋ)` of `vN_cpsuᵒᵖ`. -/
theorem su_exists_rk1_filter {z : H} (hz : ‖z‖ = 1) :
    ∃ (c : suBH H ⟶ suI.{u}) (cd : suI.{u} ⟶ suBH H),
      (∀ w : ULift.{u} ℂ, c.unop.toNCPMap w = w.down • rk1 z) ∧
      (∀ T : H →L[ℂ] H, cd.unop.toNCPMap T = ULift.up (⟪z, T z⟫ : ℂ)) := by
  have hproj : IsStarProjection (rk1 z) := rk1_isStarProjection hz
  have hzz : (⟪z, z⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz]
    norm_num
  refine ⟨Quiver.Hom.op ⟨Theses.B.Dils.ncpOfNonneg hproj.nonneg, ?_⟩,
    Quiver.Hom.op ⟨npNCP (Theses.A.VN.vectorNP z), ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · show (1 : ULift.{u} ℂ).down • rk1 z ≤ 1
    rw [show (1 : ULift.{u} ℂ).down = (1 : ℂ) from rfl, one_smul]
    exact hproj.le_one
  · show npNCP (Theses.A.VN.vectorNP z) 1 ≤ 1
    refine le_of_eq ?_
    rw [npNCP_apply]
    show ULift.up (⟪z, (1 : H →L[ℂ] H) z⟫ : ℂ) = 1
    rw [show ((1 : H →L[ℂ] H) z) = z from rfl, hzz]
    rfl

/-- **201III at a rank-one projection**: the standard filter
`c : ℂ → B(ℋ)`, `w ↦ w·|z⟩⟨z|`, is **pure** — it is `ad_{V*}` for
`V* : ℋ → ℂ`, `x ↦ ⟪z, x⟫`, after the scalar embedding `ℂ ≅ B(H₁)`, and
both are pure (`su_pure_bh_ad`, `su_isFilter_suScalarEmbed`). -/
theorem su_isPure_rk1_filter {z : H} (hz : ‖z‖ = 1) {c : suBH H ⟶ suI.{u}}
    (hcval : ∀ w : ULift.{u} ℂ, c.unop.toNCPMap w = w.down • rk1 z) : IsPure c := by
  set W : H →L[ℂ] suH1.{u} := (innerSL ℂ z).smulRight suE1.{u} with hWdef
  have hW : ∀ x : H, W x = (⟪z, x⟫ : ℂ) • suE1.{u} := fun _ => rfl
  have hWW : (ContinuousLinearMap.adjoint W) ∘L W = rk1 z := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun y => ?_
    show (⟪y, (ContinuousLinearMap.adjoint W) (W x)⟫ : ℂ) = ⟪y, rk1 z x⟫
    rw [ContinuousLinearMap.adjoint_inner_right, hW y, hW x, inner_smul_left,
      inner_smul_right, su_inner_e1_self, rk1_apply, inner_smul_right,
      inner_conj_symm]
    ring
  have hW1 : ‖W‖ ≤ 1 := by
    refine (su_conjOperator_subunital_iff W).mp ?_
    rw [su_conjOperator_one, hWW]
    exact (rk1_isStarProjection hz).le_one
  obtain ⟨E, hE⟩ : ∃ E : suBH suH1.{u} ⟶ suI.{u},
      E.unop.toNCPMap = suScalarEmbed.{u} :=
    ⟨Quiver.Hom.op ⟨suScalarEmbed.{u}, le_of_eq suScalarEmbed_one⟩, rfl⟩
  have hEp : IsPure E := by
    refine su_isPure_of_procPure ?_
    rw [hE]
    exact su_procIsPure_of_isPureMap
      (Theses.B.Dils.isPureMap_of_isFilter _ su_isFilter_suScalarEmbed)
  have hcE : c = suAdHom W hW1 ≫ E := by
    refine suop_hom_ext fun w => ?_
    have e1 : (suAdHom W hW1 ≫ E).unop.toNCPMap w
        = conjOperator W (suScalarEmbed.{u} w) :=
      Eq.trans (suop_comp_apply (suAdHom W hW1) E w)
        (congrArg (fun t => conjOperator W t) (congrArg (fun m => m w) hE))
    have e2 : conjOperator W (suScalarEmbed.{u} w) = w.down • rk1 z := by
      have e3 : suScalarEmbed.{u} w = w.down • (1 : suH1.{u} →L[ℂ] suH1.{u}) := rfl
      rw [e3, map_smul,
        show conjOperator W (1 : suH1.{u} →L[ℂ] suH1.{u})
          = (ContinuousLinearMap.adjoint W) ∘L W from su_conjOperator_one W, hWW]
    exact Eq.trans (hcval w) (Eq.trans e1 e2).symm
  rw [hcE]
  exact upm_closed_pure (su_pure_bh_ad W hW1) hEp

/-- **215VIa.2 at a rank-one projection** (bsols.tex:3400, the computation
rule the second stage of 224VI's solution names): the dagger of the standard
filter `c : ℂ → B(ℋ)`, `w ↦ w·|z⟩⟨z|`, of the rank-one projection `|z⟩⟨z|`
is the **vector state** `c† : B(ℋ) → ℂ`, `T ↦ ⟪z, T z⟫`.

`c` is pure (`su_isPure_rk1_filter`) and faithful, hence a quotient for
`(1 ∘ c)ᵖ = |z⟩⟨z|ᵖ` (`su_isQuotient_of_pure_faithful`), and
`c ≫ c† = asrt_{|z⟩⟨z|}` because `|z⟩⟨z| T |z⟩⟨z| = ⟪z, T z⟫·|z⟩⟨z|`; so
`su_dagger_of_quotient` applies.  Compare `su_dagger_standard_filter`: this
is the same rule with the corner `|z⟩⟨z|B(ℋ)|z⟩⟨z|` presented as `ℂ`. -/
theorem su_dagger_rk1_filter (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    {z : H} (hz : ‖z‖ = 1) {c : suBH H ⟶ suI.{u}} (hc : IsPure c)
    (hcval : ∀ w : ULift.{u} ℂ, c.unop.toNCPMap w = w.down • rk1 z)
    {cd : suI.{u} ⟶ suBH H}
    (hcdval : ∀ T : H →L[ℂ] H, cd.unop.toNCPMap T = ULift.up (⟪z, T z⟫ : ℂ)) :
    (d.daggerCat.dag (X := PureCat.of (suBH H)) (Y := PureCat.of suI.{u})
      ⟨c, hc⟩).1 = cd := by
  have hproj : IsStarProjection (rk1 z) := rk1_isStarProjection hz
  have hcv : ∀ w, c.unop.toNCPMap w = w.down • rk1 z := fun w => hcval w
  have hfaith : FaithfulMap c := by
    refine (su_faithfulMap_iff c).mpr fun a ha => ?_
    rw [hcv] at ha
    refine ULift.ext _ _ ?_
    exact (smul_eq_zero.mp ha).resolve_right (su_rk1_ne_zero hz)
  have hval : suPredVal (c ≫ truth suI.{u}) = rk1 z := by
    rw [suPredVal_comp, suPredVal_truth, hcv]
    show (1 : ULift.{u} ℂ).down • rk1 z = rk1 z
    rw [show (1 : ULift.{u} ℂ).down = (1 : ℂ) from rfl, one_smul]
  have hs : IsSharp (c ≫ truth suI.{u}) := by
    refine (su_isSharp_iff _).mpr ?_
    rw [hval]
    exact hproj
  have hκ : c ≫ cd = asrt (c ≫ truth suI.{u}) := by
    refine suop_hom_ext fun T => ?_
    have e1 := suop_comp_apply c cd T
    have e2 := hcv (cd.unop.toNCPMap T)
    have e3 := congrArg (fun t : ULift.{u} ℂ => t.down • rk1 z) (hcdval T)
    have e4 := su_rk1_conj z T
    have hp2 : suPredVal (c ≫ truth suI.{u}) * suPredVal (c ≫ truth suI.{u})
        = suPredVal (c ≫ truth suI.{u}) := by
      rw [hval]
      exact hproj.isIdempotentElem.eq
    have hp0 : 0 ≤ suPredVal (c ≫ truth suI.{u}) := by
      rw [hval]
      exact hproj.nonneg
    have hsqrt : CFC.sqrt (suPredVal (c ≫ truth suI.{u}))
        = suPredVal (c ≫ truth suI.{u}) := CFC.sqrt_unique hp2 hp0
    have e5 : (asrt (c ≫ truth suI.{u})).unop.toNCPMap T
        = suPredVal (c ≫ truth suI.{u}) * T
          * suPredVal (c ≫ truth suI.{u}) := by
      rw [su_asrt_apply, hsqrt]
    rw [hval] at e5
    exact e1.trans (e2.trans (e3.trans (e4.symm.trans e5.symm)))
  exact su_dagger_of_quotient d hs (su_isQuotient_of_pure_faithful hc hfaith) hc hκ

end KetBra

end PureStateClassification

/-! #### The printed route of 224VI, stages (2)-(5)

The rest of the printed solution (bsols.tex:3388-3477), on the print's own
route.  Assume `ℂ` and `ℂ` have a coproduct `𝒜` in `Pure (vNᵒᵖ)`, with
coprojections `π₁, π₂` and mediating map `h` for `id, id`.

* **(1)** `h†` is a pure *state* of `𝒜` (unital, because
  `h† ∘ π₁† = (π₁ ∘ h)† = id`), so `su_pure_state_classification` gives a
  Hilbert space `ℋ`, a von Neumann algebra `𝒞`, an nmiu-isomorphism
  `φ : B(ℋ) ⊕ 𝒞 → 𝒜` and a **unit** vector `z ∈ ℋ` with
  `h†(φ(T,c)) = ⟪z, Tz⟫`.  The whole diagram is transported along `φ`
  (`su_224VI_printed`), so that from here on the coproduct object *is*
  `B(ℋ) ⊕ 𝒞`.
* **(2)** *(bsols.tex:3399-3403)* `h† = c†_{|z⟩⟨z|} ∘ ▷₁` — both sides send
  `(T,c)` to `⟪z, Tz⟫`, by **215VIa.2** at the rank-one projection
  (`su_dagger_rk1_filter`) — and daggering gives `h = p† ∘ c_{|z⟩⟨z|}`,
  the print's formula, where `p† = suPq` is `T ↦ (T,0)`
  (`su_dagger_suPq`).  In particular `h(1) = (|z⟩⟨z|, 0)`.
* **(3)** *(bsols.tex:3404-3411)* each `π_i` is a vector state on the first
  summand, `π_i(T,c) = ⟪x_i, T x_i⟫` with `x_i` a unit vector
  (`su_224VI_vector_state`): the print's `⌈π_i ∘ φ⌉` is the minimal
  projection of `su_pure_state_minimal`, which lies in one summand
  (`su_minimalProjection_prod`) — not the second, by (2) — and is rank one
  there (`su_minimalProjection_rk1`).
* **(4)** *(bsols.tex:3412-3419)* `𝒞 = 0`.  The print applies the
  uniqueness of `h` to `φ ∘ (id ⊕ ϑ) ∘ φ⁻¹ ∘ h`; that composite is however
  *equal* to `h` for trivial reasons — by (2) the `𝒞`-component of
  `φ⁻¹ ∘ h` is already `0` — so the printed argument as it stands proves
  nothing.  The repair keeps the print's idea and applies the same
  uniqueness one step earlier, to `id` and `id ⊕ 0 = ▷₁ ∘ p†` themselves:
  both coprojections equalise them by (3), so `id = id ⊕ 0`, i.e. `𝒞 = 0`.
* **(5)** *(bsols.tex:3420-3430)* no non-zero vector is orthogonal to both
  `x₁` and `x₂` — this is the print's `dim ℋ ≤ 2`, in the form the rest of
  the argument uses — for `π_i ∘ φ ∘ p† ∘ c_{|z₀⟩⟨z₀|} = 0` for such a
  `z₀`, while `φ ∘ p† ∘ c_{|z₀⟩⟨z₀|} ≠ 0`, contradicting uniqueness
  against `0`.
* **(6)** *(bsols.tex:3437-3477)* the mediating map `f` for the two
  coprojections of `ℂ ⊕ ℂ`.  Its two values `P = f(1,0)`, `Q = f(0,1)`
  satisfy `Px₁ = x₁`, `Px₂ = 0`, `Qx₁ = 0`, `Qx₂ = x₂`, whence `x₁ ⊥ x₂`
  (which also disposes of the print's separate `dim ℋ = 1` case) and, with
  (5), `P + Q = 1`; so `f` is **total**.  A total pure map is an
  isomorphism after a comprehension (`total_pure_iso_compr`) and hence has
  **surjective** ncpsu-map (`su_compr_surjective`) — where the print
  instead identifies `⌈h(1)⌉M₂⌈h(1)⌉` and splits into cases.  Surjectivity
  is absurd: `|x₁+x₂⟩⟨x₁+x₂|` is not of the form `λP + μQ`, as pairing
  `(λP + μQ)x₁ = λx₁` with `x₂` gives `0 = 1`. -/

section PrintedRoute224VI

set_option linter.unusedSectionVars false

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- **221IIIa** (`exc-cvn-no-dilations`, eff.tex:6812, Exercise; solution
bsols.tex:3337): **the step the printed solution asserts without
argument.**

The print says: *"If `CvNᵒᵖ` were to have dilations, then any ncpu-map
would be the composition of a corner and an nmiu-map."*  It thereby takes
for granted that the `h`-leg of an abstract dilation is a **corner**, while
the definition of a dilation (**221II** `IsDilation`,
`Theses/B/Eff/Dagger.lean:3101`) only says that `h` is **pure** — a
comprehension after a quotient (**201II**).  Here is the missing argument,
proved for an arbitrary ⋄-effectus:

a **total pure map is an isomorphism followed by a comprehension** (which
is exactly what "is a corner" means, by **199VII.2** `compr_basics_2`).
Indeed, write `f = ξ ≫ π` with `ξ` a quotient for `p` and `π` a
comprehension for `q`.  Then
`1 = f ∘ 1 = ξ ∘ (π ∘ 1) ≼ ξ ∘ 1 ≼ 1`, so `ξ` is total; and a total
quotient is an isomorphism (`isIso_of_isQuotient_isTotal`, i.e. **197V.5**
`ξ ∘ 1 = pᗮ` forces `p = 0`, and **197V.2/3** then compare `ξ` with the
identity). -/
theorem total_pure_iso_compr {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] [DiamondEffectus C] {X Y : C} {f : X ⟶ Y}
    (hp : IsPure f) (ht : IsTotal f) :
    ∃ (Q : C) (θ : X ⟶ Q) (π : Q ⟶ Y) (q : Pred Y),
      IsIso θ ∧ IsComprehension q π ∧ f = θ ≫ π := by
  obtain ⟨Q, ξ, π, p, q, hξ, hπ, hf⟩ := hp
  have hξtot : IsTotal ξ := by
    show ξ ≫ truth Q = truth X
    refine eabasics_le_antisymm (pred_le_truth (ξ ≫ truth Q)) ?_
    have h1 : truth X = ξ ≫ (π ≫ truth Y) := by
      rw [← Category.assoc, ← hf]
      exact ht.symm
    rw [h1]
    exact comp_le_comp ξ (pred_le_truth (π ≫ truth Y))
  have : IsIso ξ := isIso_of_isQuotient_isTotal hξ hξtot
  exact ⟨Q, ξ, π, q, inferInstance, hπ, hf⟩

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- `0 ≤ T` and `⟪x, T x⟫ = 0` force `T x = 0`: `⟪√T x, √T x⟫ = ⟪x, T x⟫`. -/
theorem su_op_apply_eq_zero {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {x : H} (h : (⟪x, T x⟫ : ℂ) = 0) : T x = 0 := by
  have hS0 : 0 ≤ CFC.sqrt T := CFC.sqrt_nonneg T
  have hSS : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.of_nonneg hS0)
  have happ : ∀ y : H, CFC.sqrt T (CFC.sqrt T y) = T y := by
    intro y
    have h2 : (CFC.sqrt T * CFC.sqrt T) y = T y := by rw [hSS]
    exact h2
  have h1 : (⟪CFC.sqrt T x, CFC.sqrt T x⟫ : ℂ) = 0 := by
    have h3 : (⟪CFC.sqrt T x, CFC.sqrt T x⟫ : ℂ)
        = ⟪x, CFC.sqrt T (CFC.sqrt T x)⟫ := hsym x (CFC.sqrt T x)
    rw [h3, happ x, h]
  have hSx : CFC.sqrt T x = 0 := inner_self_eq_zero.mp h1
  rw [← happ x, hSx, map_zero]

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- The von Neumann algebra `𝒞` as an object of `vNᵒᵖ`. -/
noncomputable abbrev suOb (C : Type u) [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [Theses.VonNeumannAlgebra C] : WStarCPSU.{u}ᵒᵖ :=
  Opposite.op (WStarCPSU.of (WStar.of C))



/-! ### Package 3 -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- **224VI, stage (3)** (`exc-purec-no-biproduct`, eff.tex:7189; solution
bsols.tex:3388, the step "`⌈π₁ ∘ φ⌉ = (p₁,0)` for some minimal projection
`p₁`"): a minimal projection of a product `𝒜 ⊕ ℬ` lives entirely in one
summand, and is minimal there.

Both `(p₁,0)` and `(0,p₂)` are projections below `p`, so minimality makes
each of them `0` or `p`; `p ≠ 0` rules out both being `0`.  If the surviving
one is, say, `(p₁,0) = p`, then a projection `q ≤ p₁` gives the projection
`(q,0) ≤ p`, which is `0` or `p`, i.e. `q = 0` or `q = p₁`. -/
theorem su_minimalProjection_prod {A B : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {p : A × B} (hp : Theses.A.VN.IsMinimalProjection p) :
    (p.2 = 0 ∧ Theses.A.VN.IsMinimalProjection p.1) ∨
      (p.1 = 0 ∧ Theses.A.VN.IsMinimalProjection p.2) := by
  -- the two components of `p` are projections
  have h1 : IsStarProjection p.1 := by
    refine ⟨?_, ?_⟩
    · show p.1 * p.1 = p.1
      exact congrArg Prod.fst hp.1.isIdempotentElem.eq
    · show star p.1 = p.1
      exact congrArg Prod.fst hp.1.isSelfAdjoint.star_eq
  have h2 : IsStarProjection p.2 := by
    refine ⟨?_, ?_⟩
    · show p.2 * p.2 = p.2
      exact congrArg Prod.snd hp.1.isIdempotentElem.eq
    · show star p.2 = p.2
      exact congrArg Prod.snd hp.1.isSelfAdjoint.star_eq
  have hzA : IsStarProjection (0 : A) := by
    refine ⟨?_, ?_⟩
    · show (0 : A) * 0 = 0
      simp
    · show star (0 : A) = 0
      simp
  have hzB : IsStarProjection (0 : B) := by
    refine ⟨?_, ?_⟩
    · show (0 : B) * 0 = 0
      simp
    · show star (0 : B) = 0
      simp
  have hmk : ∀ (a : A) (b : B), IsStarProjection a → IsStarProjection b →
      IsStarProjection ((a, b) : A × B) := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · show ((a, b) : A × B) * (a, b) = (a, b)
      exact Prod.ext ha.isIdempotentElem.eq hb.isIdempotentElem.eq
    · show star ((a, b) : A × B) = (a, b)
      exact Prod.ext ha.isSelfAdjoint.star_eq hb.isSelfAdjoint.star_eq
  -- `(p₁, 0) ≤ p`
  have hle1 : ((p.1, (0 : B)) : A × B) ≤ p :=
    Prod.le_def.mpr ⟨le_refl _, h2.nonneg⟩
  rcases hp.2.2 _ (hmk p.1 0 h1 hzB) hle1 with hd | hd
  · -- `p.1 = 0`: the second component carries everything
    have hp1 : p.1 = 0 := congrArg Prod.fst hd
    refine Or.inr ⟨hp1, h2, ?_, ?_⟩
    · intro hp2
      exact hp.2.1 (Prod.ext hp1 hp2)
    · intro q hq hq2
      have hle : (((0 : A), q) : A × B) ≤ p :=
        Prod.le_def.mpr ⟨le_of_eq hp1.symm, hq2⟩
      rcases hp.2.2 _ (hmk 0 q hzA hq) hle with h | h
      · exact Or.inl (congrArg Prod.snd h)
      · exact Or.inr (congrArg Prod.snd h)
  · -- `p.2 = 0`: the first component carries everything
    have hp2 : p.2 = 0 := (congrArg Prod.snd hd).symm
    refine Or.inl ⟨hp2, h1, ?_, ?_⟩
    · intro hp1
      exact hp.2.1 (Prod.ext hp1 hp2)
    · intro q hq hq1
      have hle : ((q, (0 : B)) : A × B) ≤ p :=
        Prod.le_def.mpr ⟨hq1, h2.nonneg⟩
      rcases hp.2.2 _ (hmk q 0 hq hzB) hle with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (congrArg Prod.fst h)

/-! ### Package 4 -/

omit [EffectusPartialForm (WStarCPSU.{u}ᵒᵖ)] [AndThenEffectus (WStarCPSU.{u}ᵒᵖ)] in
/-- **224VI, stage (3)** (`exc-purec-no-biproduct`, eff.tex:7189; solution
bsols.tex:3388, the step "`π₁(φ(T,c)) = ⟪x, T x⟫` for some `x ∈ ℋ`"): every
minimal projection of `B(ℋ)` is a rank-one projection `|x⟩⟨x|`.

Pick `v` with `p v ≠ 0` and normalise: `x := ‖pv‖⁻¹ · pv` is a unit vector
with `p x = x` (as `p` is idempotent).  Then `p · |x⟩⟨x| = |x⟩⟨x|`
pointwise, so `|x⟩⟨x| ≤ p` (`IsStarProjection.le_iff_mul_eq_right`); and
`|x⟩⟨x| ≠ 0`, so minimality forces `|x⟩⟨x| = p`. -/
theorem su_minimalProjection_rk1 {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {p : H →L[ℂ] H}
    (hp : Theses.A.VN.IsMinimalProjection p) : ∃ x : H, ‖x‖ = 1 ∧ p = rk1 x := by
  -- a vector not killed by `p`
  obtain ⟨v, hv⟩ : ∃ v : H, p v ≠ 0 := by
    by_contra hcon
    refine hp.2.1 (ContinuousLinearMap.ext fun w => ?_)
    have hw : p w = 0 := not_not.mp fun h => hcon ⟨w, h⟩
    rw [hw]
    rfl
  have hvn : ‖p v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  obtain ⟨x, hxdef⟩ : ∃ x : H, x = (‖p v‖⁻¹ : ℝ) • p v := ⟨_, rfl⟩
  -- `x` is a unit vector fixed by `p`
  have hx1 : ‖x‖ = 1 := by
    rw [hxdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (p v))),
      inv_mul_cancel₀ hvn]
  have hpp : p (p v) = p v := by
    have h := hp.1.isIdempotentElem.eq
    calc p (p v) = (p * p) v := rfl
      _ = p v := by rw [h]
  have hsm : ((‖p v‖⁻¹ : ℝ) • p v) = (((‖p v‖⁻¹ : ℝ) : ℂ)) • p v :=
    (Complex.coe_smul _ _).symm
  have hpx : p x = x := by
    rw [hxdef, hsm, map_smul, hpp]
  -- `|x⟩⟨x|` is a non-zero projection below `p`
  have hxx : rk1 x x = x := by
    have h : (⟪x, x⟫ : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx1]
      norm_num
    rw [rk1_apply, h, one_smul]
  have hne : rk1 x ≠ 0 := by
    intro h0
    rw [h0] at hxx
    have hz0 : (0 : H →L[ℂ] H) x = 0 := rfl
    have hx0 : x = 0 := hxx.symm.trans hz0
    rw [hx0, norm_zero] at hx1
    exact zero_ne_one hx1
  have hproj : IsStarProjection (rk1 x) := rk1_isStarProjection hx1
  have hmul : p * rk1 x = rk1 x := by
    refine ContinuousLinearMap.ext fun y => ?_
    show p (rk1 x y) = rk1 x y
    rw [rk1_apply, map_smul, hpx]
  have hle : rk1 x ≤ p :=
    (IsStarProjection.le_iff_mul_eq_right hproj hp.1).mpr hmul
  rcases hp.2.2 _ hproj hle with h | h
  · exact absurd h hne
  · exact ⟨x, hx1, h.symm⟩

/-! ### Package 2 -/


/-- **224VI, stage (4)** (`exc-purec-no-biproduct`, eff.tex:7189; solution
bsols.tex:3388): the map `p† : X ⟶ X + Y` of `vN_cpsuᵒᵖ` given by the
algebra map `a ↦ (a,0)` — the dagger of the regular coprojection
`p = κ₁` of the solution.  (`suPinl X Y` is `κ₁` itself, the algebra
projection `(a,b) ↦ a`.) -/
noncomputable def suPq (X Y : WStarCPSU.{u}ᵒᵖ) : suP X Y ⟶ X :=
  Quiver.Hom.op
    (wPairSU (𝟙 X.unop) (wZeroSU X.unop.base.carrier Y.unop.base.carrier))

@[simp] theorem suPq_apply (X Y : WStarCPSU.{u}ᵒᵖ) (a : X.unop.base.carrier) :
    (suPq X Y).unop.toNCPMap a = (a, 0) :=
  Prod.ext (su_id_apply a) rfl

/-- **224VI, stage (4)**: `a ↦ (a,0)` is a **filter** (proc.tex 96I) for the
effect `(1,0)`.  Given an ncp map `f : Z → X ⊕ Y` with `f(1) ≤ (1,0)`, its
second component `f₂` satisfies `0 ≤ f₂(1) ≤ 0`, hence is zero
(`su_ncp_eq_zero_of_one`); so `f(z) = ((f z).1, 0)` and the first component
of `f` is the (visibly unique) mediating map. -/
theorem su_isFilter_suPq (X Y : WStarCPSU.{u}ᵒᵖ) :
    Theses.A.Proc.IsFilter (suPq X Y).unop.toNCPMap := by
  constructor
  intro Z hZ1 hZ2 hZ3 hZ4 f hf1
  rw [suPq_apply] at hf1
  obtain ⟨f₁, hf₁⟩ := Theses.A.Proc.exists_ncpComp
    (wFstSU X.unop.base.carrier Y.unop.base.carrier).toNCPMap f
  obtain ⟨f₂, hf₂⟩ := Theses.A.Proc.exists_ncpComp
    (wSndSU X.unop.base.carrier Y.unop.base.carrier).toNCPMap f
  have hf₁' : ∀ z : Z, f₁ z = (f z).1 := fun z => hf₁ z
  have hf₂' : ∀ z : Z, f₂ z = (f z).2 := fun z => hf₂ z
  -- the second component of `f` is zero
  have hle2 : f₂ 1 ≤ 0 := by
    rw [hf₂' 1]
    exact (Prod.le_def.mp hf1).2
  have hpos2 : (0 : Y.unop.base.carrier) ≤ f₂ 1 := by
    have h := OrderHomClass.mono f₂.toCompletelyPositiveMap (zero_le_one' Z)
    rwa [map_zero] at h
  have hz2 : ∀ z : Z, (f z).2 = 0 := by
    intro z
    rw [← hf₂' z]
    exact ncp_eq_zero_of_one f₂ (le_antisymm hle2 hpos2) z
  refine ⟨f₁, fun b => ?_, fun g hg => ?_⟩
  · rw [suPq_apply]
    exact Prod.ext (hf₁' b).symm (hz2 b)
  · refine DFunLike.ext _ _ fun b => ?_
    have h := hg b
    rw [suPq_apply] at h
    exact (congrArg Prod.fst h).symm.trans (hf₁' b).symm

/-- **224VI, stage (4)**: `a ↦ (a,0)` is a **quotient** for `(1,0)ᵖ`, by
197IV at `vNᵒᵖ` (`su_isQuotient_of_isFilter`): it is a filter taking the
value `(1,0) = (1,0)ᵖᵖ` at `1`. -/
theorem su_isQuotient_suPq (X Y : WStarCPSU.{u}ᵒᵖ) :
    IsQuotient (EffectusPartialForm.orth (suPq X Y ≫ truth X)) (suPq X Y) := by
  refine su_isQuotient_of_isFilter _ _ (su_isFilter_suPq X Y) ?_
  have hoo : EffectusPartialForm.orth
      (EffectusPartialForm.orth (suPq X Y ≫ truth X)) = suPq X Y ≫ truth X :=
    eabasics_orth_orth _
  rw [hoo, suPredVal_comp, suPredVal_truth]

/-- **224VI, stage (4)**: `a ↦ (a,0)` is **pure**, being a quotient
(`isPure_of_isQuotient`). -/
theorem su_isPure_suPq (X Y : WStarCPSU.{u}ᵒᵖ) : IsPure (suPq X Y) :=
  isPure_of_isQuotient (su_isQuotient_suPq X Y)

/-- **224VI, stage (4)** (bsols.tex:3388, "the regular coprojection
`(T,c) ↦ T`, which is corner with `p†(T) = (T,0)`"): the dagger of the
quotient `a ↦ (a,0)` is the coprojection `κ₁ : (a,b) ↦ a`.

By 216VII without the choice (`su_dagger_of_quotient`) it suffices that
`s := (1,0)` is sharp — it is a projection, `su_isSharp_iff` — and that
`suPq ≫ κ₁ = asrt_s`; both sides send `(a,b)` to `(a,0)`, the right-hand
side because `√(1,0) = (1,0)` (a projection is its own square root). -/
theorem su_dagger_suPq (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    (X Y : WStarCPSU.{u}ᵒᵖ) :
    (d.daggerCat.dag (X := PureCat.of (suP X Y)) (Y := PureCat.of X)
      ⟨suPq X Y, su_isPure_suPq X Y⟩).1 = suPinl X Y := by
  have hval : suPredVal (suPq X Y ≫ truth X)
      = ((1 : X.unop.base.carrier), (0 : Y.unop.base.carrier)) := by
    rw [suPredVal_comp, suPredVal_truth, suPq_apply]
  have hp10 : IsStarProjection
      ((1, 0) : X.unop.base.carrier × Y.unop.base.carrier) := by
    refine ⟨?_, ?_⟩
    · show ((1, 0) : X.unop.base.carrier × Y.unop.base.carrier) * (1, 0) = (1, 0)
      refine Prod.ext ?_ ?_
      · show (1 : X.unop.base.carrier) * 1 = 1
        rw [one_mul]
      · show (0 : Y.unop.base.carrier) * 0 = 0
        rw [mul_zero]
    · show star ((1, 0) : X.unop.base.carrier × Y.unop.base.carrier) = (1, 0)
      refine Prod.ext ?_ ?_
      · show star (1 : X.unop.base.carrier) = 1
        simp
      · show star (0 : Y.unop.base.carrier) = 0
        simp
  have hproj : IsStarProjection (suPredVal (suPq X Y ≫ truth X)) := by
    rw [hval]
    exact hp10
  have hs : IsSharp (suPq X Y ≫ truth X) := (su_isSharp_iff _).mpr hproj
  have hsqrt : CFC.sqrt (suPredVal (suPq X Y ≫ truth X))
      = suPredVal (suPq X Y ≫ truth X) :=
    CFC.sqrt_unique hproj.isIdempotentElem.eq hproj.nonneg
  have hκ : suPq X Y ≫ suPinl X Y = asrt (suPq X Y ≫ truth X) := by
    refine suop_hom_ext fun x => ?_
    have e1 : (suPq X Y ≫ suPinl X Y).unop.toNCPMap x = (x.1, 0) := by
      rw [suop_comp_apply]
      show (suPq X Y).unop.toNCPMap x.1 = (x.1, 0)
      exact suPq_apply X Y x.1
    have e2 : (asrt (suPq X Y ≫ truth X)).unop.toNCPMap x = (x.1, 0) := by
      rw [su_asrt_apply, hsqrt, hval]
      refine Prod.ext ?_ ?_
      · show (1 : X.unop.base.carrier) * x.1 * 1 = x.1
        rw [one_mul, mul_one]
      · show (0 : Y.unop.base.carrier) * x.2 * 0 = 0
        rw [zero_mul, zero_mul]
    exact e1.trans e2.symm
  exact su_dagger_of_quotient d hs (su_isQuotient_suPq X Y)
    (su_isPure_suPq X Y) hκ

/-- **224VI, stage (4)**: the coprojection `κ₁ : X ⟶ X + Y` of `vN_cpsuᵒᵖ`
is **pure** — it is the dagger of the pure map `suPq` (`su_dagger_suPq`),
and daggers are morphisms of `Pure (vNᵒᵖ)`.  (`vNᵒᵖ` has a dagger,
`su_daggerEffectus`; `IsPure` is a `Prop`, so the choice is harmless.) -/
theorem su_isPure_suPinl (X Y : WStarCPSU.{u}ᵒᵖ) : IsPure (suPinl X Y) := by
  obtain ⟨d⟩ := su_daggerEffectus.{u}
  rw [← su_dagger_suPq d X Y]
  exact (d.daggerCat.dag (X := PureCat.of (suP X Y)) (Y := PureCat.of X)
    ⟨suPq X Y, su_isPure_suPq X Y⟩).2



/-! ### 224VI, the printed route -/

section Printed

variable {K C : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [Theses.VonNeumannAlgebra C]

/-- **bsols.tex:3402-3411**: a pure state of `B(ℋ) ⊕ 𝒞` which does not kill
`(|z⟩⟨z|, 0)` is the vector state of a unit vector `x ∈ ℋ` on the first
summand. -/
theorem su_224VI_vector_state
    (hmin_prod : ∀ p : (K →L[ℂ] K) × C, Theses.A.VN.IsMinimalProjection p →
      (p.2 = 0 ∧ Theses.A.VN.IsMinimalProjection p.1) ∨
        (p.1 = 0 ∧ Theses.A.VN.IsMinimalProjection p.2))
    (hmin_rk1 : ∀ p : K →L[ℂ] K, Theses.A.VN.IsMinimalProjection p →
      ∃ x : K, ‖x‖ = 1 ∧ p = rk1 x)
    (i : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP (suBH K) (suOb C)))
    {z : K} (hz : ‖z‖ = 1)
    (hone : i.1.unop.toNCPMap ((rk1 z, 0) : (K →L[ℂ] K) × C)
      = (1 : ULift.{u} ℂ)) :
    ∃ x : K, ‖x‖ = 1 ∧ ∀ a : (K →L[ℂ] K) × C,
      i.1.unop.toNCPMap a = ULift.up (⟪x, a.1 x⟫ : ℂ) := by
  have hproj : IsStarProjection (rk1 z) := rk1_isStarProjection hz
  have hpure : Theses.B.Dils.IsPureMap i.1.unop.toNCPMap :=
    Theses.B.Dils.isPureMap_of_procIsPure (su_procPure_of_isPure i.2)
  have hle : ((rk1 z, 0) : (K →L[ℂ] K) × C) ≤ (1 : (K →L[ℂ] K) × C) :=
    Prod.le_def.mpr ⟨hproj.le_one, zero_le_one⟩
  have hf1 : i.1.unop.toNCPMap (1 : (K →L[ℂ] K) × C) = (1 : ULift.{u} ℂ) := by
    refine le_antisymm i.1.unop.subunital' ?_
    have h : i.1.unop.toNCPMap ((rk1 z, 0) : (K →L[ℂ] K) × C)
        ≤ i.1.unop.toNCPMap (1 : (K →L[ℂ] K) × C) := ncpsu_mono i.1.unop hle
    rwa [hone] at h
  have hf1d : (i.1.unop.toNCPMap (1 : (K →L[ℂ] K) × C)).down = (1 : ℂ) := by
    rw [hf1]
    rfl
  have hf1ne : i.1.unop.toNCPMap (1 : (K →L[ℂ] K) × C) ≠ 0 := by
    intro h0
    have h1 : (1 : ℂ) = 0 := by
      rw [← hf1d, h0]
      rfl
    exact one_ne_zero h1
  obtain ⟨p₀, hp₀, hpf₀⟩ := su_pure_state_minimal i.1.unop.toNCPMap hpure hf1ne
  obtain ⟨p, hpeq⟩ : ∃ p : (K →L[ℂ] K) × C, p = p₀ := ⟨p₀, rfl⟩
  have hp : Theses.A.VN.IsMinimalProjection p := by rw [hpeq]; exact hp₀
  have hpf : ∀ a : (K →L[ℂ] K) × C,
      (i.1.unop.toNCPMap a).down • p
        = (i.1.unop.toNCPMap (1 : (K →L[ℂ] K) × C)).down • (p * a * p) := by
    intro a
    rw [hpeq]
    exact hpf₀ a
  rcases hmin_prod p hp with ⟨hp2, hp1⟩ | ⟨hp1, hp2⟩
  · obtain ⟨x, hx1, hxp⟩ := hmin_rk1 p.1 hp1
    refine ⟨x, hx1, fun a => ?_⟩
    have h := hpf a
    rw [hf1d, one_smul] at h
    have h1 : (i.1.unop.toNCPMap a).down • p.1 = p.1 * a.1 * p.1 :=
      congrArg Prod.fst h
    rw [hxp, su_rk1_conj] at h1
    have hne : rk1 x ≠ 0 := su_rk1_ne_zero hx1
    refine ULift.ext _ _ ?_
    have h2 : ((i.1.unop.toNCPMap a).down - (⟪x, a.1 x⟫ : ℂ)) • rk1 x = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hne)
  · exfalso
    refine hp.ne_zero ?_
    have h := hpf ((rk1 z, 0) : (K →L[ℂ] K) × C)
    rw [hone, hf1d, one_smul,
      show ((1 : ULift.{u} ℂ).down : ℂ) = 1 from rfl, one_smul] at h
    refine Prod.ext hp1 ?_
    · have h3 : p.2 = p.2 * 0 * p.2 := congrArg Prod.snd h
      rw [mul_zero, zero_mul] at h3
      exact h3

/-- **Stages (2)-(5) of the printed solution of 224VI** (bsols.tex:3388-3477),
run at the transported coproduct: the coproduct object is the direct sum
`B(K) ⊕ 𝒞` of the classification, `i₁ i₂` are its two coprojections, `m` is
the mediating map for `id, id`, and `m†` is the vector state at `z`.  There
is no such diagram. -/
theorem su_224VI_false
    (d : DaggerEffectus (WStarCPSU.{u}ᵒᵖ))
    (hmin_prod : ∀ p : (K →L[ℂ] K) × C, Theses.A.VN.IsMinimalProjection p →
      (p.2 = 0 ∧ Theses.A.VN.IsMinimalProjection p.1) ∨
        (p.1 = 0 ∧ Theses.A.VN.IsMinimalProjection p.2))
    (hmin_rk1 : ∀ p : K →L[ℂ] K, Theses.A.VN.IsMinimalProjection p →
      ∃ x : K, ‖x‖ = 1 ∧ p = rk1 x)
    (Qm : (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suBH K))
    (hQm : ∀ T : K →L[ℂ] K,
      Qm.1.unop.toNCPMap T = ((T, 0) : (K →L[ℂ] K) × C))
    (Inl : (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP (suBH K) (suOb C)))
    (hInl : ∀ a : (K →L[ℂ] K) × C, Inl.1.unop.toNCPMap a = a.1)
    (hdagQ : d.daggerCat.dag Qm = Inl)
    (pl pr : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP suI.{u} suI.{u}))
    (hpl : ∀ a : ULift.{u} ℂ × ULift.{u} ℂ, pl.1.unop.toNCPMap a = a.1)
    (hpr : ∀ a : ULift.{u} ℂ × ULift.{u} ℂ, pr.1.unop.toNCPMap a = a.2)
    (i₁ i₂ : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP (suBH K) (suOb C)))
    (m : (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of suI.{u})
    (hm1 : i₁ ≫ m = 𝟙 _) (hm2 : i₂ ≫ m = 𝟙 _)
    (hext : ∀ (W : PureCat (WStarCPSU.{u}ᵒᵖ))
      (u v : (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ W),
      i₁ ≫ u = i₁ ≫ v → i₂ ≫ u = i₂ ≫ v → u = v)
    (hmed : ∀ (W : PureCat (WStarCPSU.{u}ᵒᵖ))
      (a b : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ W),
      ∃ w : (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ W,
        i₁ ≫ w = a ∧ i₂ ≫ w = b)
    {z : K} (hz : ‖z‖ = 1)
    (hdagm : ∀ a : (K →L[ℂ] K) × C,
      (d.daggerCat.dag m).1.unop.toNCPMap a = ULift.up (⟪z, a.1 z⟫ : ℂ)) :
    False := by
  -- **(2)** `m = Q ∘ c_{|z⟩⟨z|}`, by daggering `m† = c† ∘ ▷₁`
  obtain ⟨c, cd, hc, hcd⟩ := su_exists_rk1_filter (H := K) hz
  have hcp : IsPure c := su_isPure_rk1_filter hz hc
  have hdagc : (d.daggerCat.dag (⟨c, hcp⟩ :
      (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1
      = cd := su_dagger_rk1_filter d hz hcp hc hcd
  have key : d.daggerCat.dag m
      = d.daggerCat.dag (⟨c, hcp⟩ :
        (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})
        ≫ Inl := by
    refine Subtype.ext (suop_hom_ext fun a => ?_)
    have hrhs : (d.daggerCat.dag (⟨c, hcp⟩ :
        (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})
        ≫ Inl).1.unop.toNCPMap a
        = (d.daggerCat.dag (⟨c, hcp⟩ :
          (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
            PureCat.of suI.{u})).1.unop.toNCPMap (Inl.1.unop.toNCPMap a) :=
      suop_comp_apply (d.daggerCat.dag (⟨c, hcp⟩ :
        (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
          PureCat.of suI.{u})).1 Inl.1 a
    rw [hrhs, hdagc, hInl (a : (K →L[ℂ] K) × C),
      hcd ((a : (K →L[ℂ] K) × C).1), hdagm (a : (K →L[ℂ] K) × C)]
  have hm : m = Qm ≫ ⟨c, hcp⟩ := by
    have h := congrArg d.daggerCat.dag key
    rw [d.daggerCat.dag_dag, d.daggerCat.dag_comp, d.daggerCat.dag_dag, ← hdagQ,
      d.daggerCat.dag_dag] at h
    exact h
  have hc1 : c.unop.toNCPMap (1 : ULift.{u} ℂ) = rk1 z := by
    rw [hc]
    show (1 : ℂ) • rk1 z = rk1 z
    rw [one_smul]
  have hmval : m.1.unop.toNCPMap (1 : ULift.{u} ℂ)
      = ((rk1 z, 0) : (K →L[ℂ] K) × C) := by
    have h1 : m.1.unop.toNCPMap (1 : ULift.{u} ℂ)
        = Qm.1.unop.toNCPMap (c.unop.toNCPMap (1 : ULift.{u} ℂ)) := by
      have h2 : (Qm ≫ (⟨c, hcp⟩ : (PureCat.of (suBH K) :
          PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1.unop.toNCPMap
            (1 : ULift.{u} ℂ)
          = Qm.1.unop.toNCPMap (c.unop.toNCPMap (1 : ULift.{u} ℂ)) :=
        suop_comp_apply Qm.1 c (1 : ULift.{u} ℂ)
      rw [hm]
      exact h2
    rw [h1, hc1, hQm]
  -- both coprojections take the value `1` at `(|z⟩⟨z|, 0)`
  have hone : ∀ (i : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP (suBH K) (suOb C))), i ≫ m = 𝟙 _ →
      i.1.unop.toNCPMap ((rk1 z, 0) : (K →L[ℂ] K) × C) = (1 : ULift.{u} ℂ) := by
    intro i hi
    have hval : i.1 ≫ m.1 = 𝟙 (suI.{u}) := congrArg Subtype.val hi
    have h : (i.1 ≫ m.1).unop.toNCPMap (1 : ULift.{u} ℂ)
        = (𝟙 suI.{u}).unop.toNCPMap (1 : ULift.{u} ℂ) :=
      congrArg (fun t : suI.{u} ⟶ suI.{u} => t.unop.toNCPMap (1 : ULift.{u} ℂ))
        hval
    rw [suop_comp_apply i.1 m.1 (1 : ULift.{u} ℂ), hmval,
      suop_id_apply (X := suI.{u}) (1 : ULift.{u} ℂ)] at h
    exact h
  obtain ⟨x₁, hx₁n, hx₁⟩ :=
    su_224VI_vector_state hmin_prod hmin_rk1 i₁ hz (hone i₁ hm1)
  obtain ⟨x₂, hx₂n, hx₂⟩ :=
    su_224VI_vector_state hmin_prod hmin_rk1 i₂ hz (hone i₂ hm2)
  have hx₁self : (⟪x₁, x₁⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx₁n]
    norm_num
  have hx₂self : (⟪x₂, x₂⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx₂n]
    norm_num
  -- **(3)** `𝒞 = 0`
  have hstep : ∀ (i : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      PureCat.of (suP (suBH K) (suOb C))) (y : K),
      (∀ a : (K →L[ℂ] K) × C, i.1.unop.toNCPMap a = ULift.up (⟪y, a.1 y⟫ : ℂ)) →
      i ≫ (Qm ≫ Inl) = i := by
    intro i y hy
    refine Subtype.ext (suop_hom_ext fun a => ?_)
    have h1 : (i ≫ Qm ≫ Inl).1.unop.toNCPMap a
        = i.1.unop.toNCPMap ((Qm ≫ Inl).1.unop.toNCPMap a) :=
      suop_comp_apply i.1 (Qm ≫ Inl).1 a
    have h2 : (Qm ≫ Inl).1.unop.toNCPMap a
        = Qm.1.unop.toNCPMap (Inl.1.unop.toNCPMap a) :=
      suop_comp_apply Qm.1 Inl.1 a
    rw [h1, h2, hInl (a : (K →L[ℂ] K) × C), hQm ((a : (K →L[ℂ] K) × C).1),
      hy (((a : (K →L[ℂ] K) × C).1, 0) : (K →L[ℂ] K) × C),
      hy (a : (K →L[ℂ] K) × C)]
  have hQI : Qm ≫ Inl = 𝟙 (PureCat.of (suP (suBH K) (suOb C))) := by
    refine hext _ _ _ ?_ ?_
    · rw [Category.comp_id]
      exact hstep i₁ x₁ hx₁
    · rw [Category.comp_id]
      exact hstep i₂ x₂ hx₂
  have hCzero : ∀ w : C, w = 0 := by
    intro w
    have hval : Qm.1 ≫ Inl.1 = 𝟙 (suP (suBH K) (suOb C)) := congrArg Subtype.val hQI
    have h : (Qm.1 ≫ Inl.1).unop.toNCPMap ((0, w) : (K →L[ℂ] K) × C)
        = (𝟙 (suP (suBH K) (suOb C))).unop.toNCPMap ((0, w) : (K →L[ℂ] K) × C) :=
      congrArg (fun t : suP (suBH K) (suOb C) ⟶ suP (suBH K) (suOb C) =>
        t.unop.toNCPMap ((0, w) : (K →L[ℂ] K) × C)) hval
    rw [suop_comp_apply Qm.1 Inl.1 ((0, w) : (K →L[ℂ] K) × C),
      hInl ((0, w) : (K →L[ℂ] K) × C), hQm (0 : K →L[ℂ] K),
      suop_id_apply (X := suP (suBH K) (suOb C))
        ((0, w) : (K →L[ℂ] K) × C)] at h
    exact (congrArg Prod.snd h).symm
  -- **(4)** nothing is orthogonal to both `x₁` and `x₂` ("`dim ℋ ≤ 2`")
  have hspan : ∀ v : K, (⟪x₁, v⟫ : ℂ) = 0 → (⟪x₂, v⟫ : ℂ) = 0 → v = 0 := by
    intro v h1 h2
    by_contra hv
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hz₀ : ‖((‖v‖ : ℂ))⁻¹ • v‖ = 1 := by
      rw [norm_smul]
      simp [hvn]
    obtain ⟨c₀, cd₀, hc₀, -⟩ := su_exists_rk1_filter (H := K) hz₀
    have hc₀p : IsPure c₀ := su_isPure_rk1_filter hz₀ hc₀
    have hxz : ∀ y : K, (⟪y, v⟫ : ℂ) = 0 → (⟪y, ((‖v‖ : ℂ))⁻¹ • v⟫ : ℂ) = 0 := by
      intro y hy
      rw [inner_smul_right, hy, mul_zero]
    have hzero : ∀ (i : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
        PureCat.of (suP (suBH K) (suOb C))) (y : K),
        (∀ a : (K →L[ℂ] K) × C,
          i.1.unop.toNCPMap a = ULift.up (⟪y, a.1 y⟫ : ℂ)) →
        (⟪y, ((‖v‖ : ℂ))⁻¹ • v⟫ : ℂ) = 0 →
        i ≫ (Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
            PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u}))
          = i ≫ (⟨(0 : suP (suBH K) (suOb C) ⟶ suI.{u}), isPure_zero⟩ :
            (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
              PureCat.of suI.{u}) := by
      intro i y hy hyz
      refine Subtype.ext (suop_hom_ext fun w => ?_)
      have e1 : (i ≫ Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
          PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1.unop.toNCPMap w
          = i.1.unop.toNCPMap ((Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
            PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
              PureCat.of suI.{u})).1.unop.toNCPMap w) :=
        suop_comp_apply i.1 (Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
          PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1 w
      have e2 : (Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
          PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1.unop.toNCPMap w
          = Qm.1.unop.toNCPMap (c₀.unop.toNCPMap w) :=
        suop_comp_apply Qm.1 c₀ w
      have e3 : (i ≫ (⟨(0 : suP (suBH K) (suOb C) ⟶ suI.{u}), isPure_zero⟩ :
          (PureCat.of (suP (suBH K) (suOb C)) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
            PureCat.of suI.{u})).1.unop.toNCPMap w
          = i.1.unop.toNCPMap
            ((0 : suP (suBH K) (suOb C) ⟶ suI.{u}).unop.toNCPMap w) :=
        suop_comp_apply i.1 (0 : suP (suBH K) (suOb C) ⟶ suI.{u}) w
      have hz2 : (⟪y, ((w.down • rk1 (((‖v‖ : ℂ))⁻¹ • v) : K →L[ℂ] K)) y⟫ : ℂ)
          = 0 := by
        rw [smul_apply, rk1_apply, inner_smul_right,
          inner_smul_right, hyz, mul_zero, mul_zero]
      rw [e1, e2, e3, hc₀ w, hQm (w.down • rk1 (((‖v‖ : ℂ))⁻¹ • v)),
        hy ((w.down • rk1 (((‖v‖ : ℂ))⁻¹ • v), 0) : (K →L[ℂ] K) × C),
        show ((0 : suP (suBH K) (suOb C) ⟶ suI.{u}).unop.toNCPMap w)
          = (0 : (K →L[ℂ] K) × C) from rfl,
        hy (0 : (K →L[ℂ] K) × C)]
      have hz3 : (⟪y, ((0 : (K →L[ℂ] K) × C).1) y⟫ : ℂ) = 0 := by
        show (⟪y, (0 : K →L[ℂ] K) y⟫ : ℂ) = 0
        rw [show ((0 : K →L[ℂ] K) y) = 0 from rfl, inner_zero_right]
      rw [hz3]
      exact congrArg ULift.up hz2
    have hNz : Qm ≫ (⟨c₀, hc₀p⟩ :
        (PureCat.of (suBH K) : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})
        = ⟨(0 : suP (suBH K) (suOb C) ⟶ suI.{u}), isPure_zero⟩ :=
      hext _ _ _ (hzero i₁ x₁ hx₁ (hxz x₁ h1)) (hzero i₂ x₂ hx₂ (hxz x₂ h2))
    have hval : (Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
        PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1.unop.toNCPMap
          (1 : ULift.{u} ℂ)
        = (0 : suP (suBH K) (suOb C) ⟶ suI.{u}).unop.toNCPMap
          (1 : ULift.{u} ℂ) :=
      congrArg (fun t : (PureCat.of (suP (suBH K) (suOb C)) :
        PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u} =>
        t.1.unop.toNCPMap (1 : ULift.{u} ℂ)) hNz
    have e4 : (Qm ≫ (⟨c₀, hc₀p⟩ : (PureCat.of (suBH K) :
        PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ PureCat.of suI.{u})).1.unop.toNCPMap
          (1 : ULift.{u} ℂ)
        = Qm.1.unop.toNCPMap (c₀.unop.toNCPMap (1 : ULift.{u} ℂ)) :=
      suop_comp_apply Qm.1 c₀ (1 : ULift.{u} ℂ)
    have hc₀1 : c₀.unop.toNCPMap (1 : ULift.{u} ℂ) = rk1 (((‖v‖ : ℂ))⁻¹ • v) := by
      rw [hc₀]
      show (1 : ℂ) • rk1 (((‖v‖ : ℂ))⁻¹ • v) = _
      rw [one_smul]
    rw [e4, hc₀1, hQm (rk1 (((‖v‖ : ℂ))⁻¹ • v)),
      show ((0 : suP (suBH K) (suOb C) ⟶ suI.{u}).unop.toNCPMap
        (1 : ULift.{u} ℂ)) = (0 : (K →L[ℂ] K) × C) from rfl] at hval
    exact su_rk1_ne_zero hz₀ (congrArg Prod.fst hval)
  -- **(5)** the mediating map for the two coprojections of `ℂ ⊕ ℂ`
  obtain ⟨F, hF1, hF2⟩ := hmed (PureCat.of (suP suI.{u} suI.{u})) pl pr
  have hFadd : ∀ x y : ULift.{u} ℂ × ULift.{u} ℂ,
      F.1.unop.toNCPMap (x + y)
        = F.1.unop.toNCPMap x + F.1.unop.toNCPMap y :=
    fun x y => ncp_add_apply F.1.unop.toNCPMap x y
  have hFsmul : ∀ (r : ℂ) (x : ULift.{u} ℂ × ULift.{u} ℂ),
      F.1.unop.toNCPMap (r • x) = r • F.1.unop.toNCPMap x :=
    fun r x => ncp_smul_apply F.1.unop.toNCPMap r x
  have hFzero : F.1.unop.toNCPMap (0 : ULift.{u} ℂ × ULift.{u} ℂ)
      = (0 : (K →L[ℂ] K) × C) := ncp_zero_apply F.1.unop.toNCPMap
  have hv1 : ∀ (b : ULift.{u} ℂ × ULift.{u} ℂ) (t : (K →L[ℂ] K) × C),
      F.1.unop.toNCPMap b = t → (⟪x₁, t.1 x₁⟫ : ℂ) = b.1.down := by
    intro b t hbt
    have hval : i₁.1 ≫ F.1 = pl.1 := congrArg Subtype.val hF1
    have h : (i₁.1 ≫ F.1).unop.toNCPMap b = pl.1.unop.toNCPMap b :=
      congrArg (fun s : suI.{u} ⟶ suP suI.{u} suI.{u} => s.unop.toNCPMap b) hval
    rw [suop_comp_apply i₁.1 F.1 b, hbt, hx₁ t, hpl b] at h
    exact congrArg ULift.down h
  have hv2 : ∀ (b : ULift.{u} ℂ × ULift.{u} ℂ) (t : (K →L[ℂ] K) × C),
      F.1.unop.toNCPMap b = t → (⟪x₂, t.1 x₂⟫ : ℂ) = b.2.down := by
    intro b t hbt
    have hval : i₂.1 ≫ F.1 = pr.1 := congrArg Subtype.val hF2
    have h : (i₂.1 ≫ F.1).unop.toNCPMap b = pr.1.unop.toNCPMap b :=
      congrArg (fun s : suI.{u} ⟶ suP suI.{u} suI.{u} => s.unop.toNCPMap b) hval
    rw [suop_comp_apply i₂.1 F.1 b, hbt, hx₂ t, hpr b] at h
    exact congrArg ULift.down h
  have hnn : ∀ b : ULift.{u} ℂ × ULift.{u} ℂ,
      (0 : ULift.{u} ℂ × ULift.{u} ℂ) ≤ b →
      (0 : (K →L[ℂ] K) × C) ≤ F.1.unop.toNCPMap b := by
    intro b hb
    have h : F.1.unop.toNCPMap (0 : ULift.{u} ℂ × ULift.{u} ℂ)
        ≤ F.1.unop.toNCPMap b := ncpsu_mono F.1.unop hb
    rwa [hFzero] at h
  have hsub : ∀ b : ULift.{u} ℂ × ULift.{u} ℂ,
      b ≤ (1 : ULift.{u} ℂ × ULift.{u} ℂ) →
      F.1.unop.toNCPMap b ≤ (1 : (K →L[ℂ] K) × C) :=
    fun b hb => (ncpsu_mono F.1.unop hb).trans F.1.unop.subunital'
  have he1 : (0 : ULift.{u} ℂ × ULift.{u} ℂ)
      ≤ ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ) :=
    Prod.le_def.mpr ⟨zero_le_one, le_refl 0⟩
  have he2 : (0 : ULift.{u} ℂ × ULift.{u} ℂ)
      ≤ ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) :=
    Prod.le_def.mpr ⟨le_refl 0, zero_le_one⟩
  have he1' : ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ) ≤ 1 :=
    Prod.le_def.mpr ⟨le_refl 1, zero_le_one⟩
  have he2' : ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) ≤ 1 :=
    Prod.le_def.mpr ⟨zero_le_one, le_refl 1⟩
  obtain ⟨tP, htP⟩ : ∃ t : (K →L[ℂ] K) × C,
      F.1.unop.toNCPMap ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ) = t := ⟨_, rfl⟩
  obtain ⟨tQ, htQ⟩ : ∃ t : (K →L[ℂ] K) × C,
      F.1.unop.toNCPMap ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) = t := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : K →L[ℂ] K, P = tP.1 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : K →L[ℂ] K, Q = tQ.1 := ⟨_, rfl⟩
  have htP0 : (0 : (K →L[ℂ] K) × C) ≤ tP := by
    rw [← htP]
    exact hnn _ he1
  have htQ0 : (0 : (K →L[ℂ] K) × C) ≤ tQ := by
    rw [← htQ]
    exact hnn _ he2
  have htP1 : tP ≤ (1 : (K →L[ℂ] K) × C) := by
    rw [← htP]
    exact hsub _ he1'
  have htQ1 : tQ ≤ (1 : (K →L[ℂ] K) × C) := by
    rw [← htQ]
    exact hsub _ he2'
  have hP0 : (0 : K →L[ℂ] K) ≤ P := by
    rw [hPdef]
    exact (Prod.le_def.mp htP0).1
  have hQ0 : (0 : K →L[ℂ] K) ≤ Q := by
    rw [hQdef]
    exact (Prod.le_def.mp htQ0).1
  have hP1 : P ≤ (1 : K →L[ℂ] K) := by
    rw [hPdef]
    exact (Prod.le_def.mp htP1).1
  have hQ1 : Q ≤ (1 : K →L[ℂ] K) := by
    rw [hQdef]
    exact (Prod.le_def.mp htQ1).1
  have hPv1 : (⟪x₁, P x₁⟫ : ℂ) = 1 := by
    rw [hPdef]
    exact hv1 ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ) tP htP
  have hPv2 : (⟪x₂, P x₂⟫ : ℂ) = 0 := by
    rw [hPdef]
    exact hv2 ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ) tP htP
  have hQv1 : (⟪x₁, Q x₁⟫ : ℂ) = 0 := by
    rw [hQdef]
    exact hv1 ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) tQ htQ
  have hQv2 : (⟪x₂, Q x₂⟫ : ℂ) = 1 := by
    rw [hQdef]
    exact hv2 ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) tQ htQ
  have hPx₂ : P x₂ = 0 := su_op_apply_eq_zero hP0 hPv2
  have hQx₁ : Q x₁ = 0 := su_op_apply_eq_zero hQ0 hQv1
  have hPx₁ : P x₁ = x₁ := by
    have h0 : (0 : K →L[ℂ] K) ≤ 1 - P := sub_nonneg.mpr hP1
    have h1 : (⟪x₁, ((1 : K →L[ℂ] K) - P) x₁⟫ : ℂ) = 0 := by
      have h2 : ((1 : K →L[ℂ] K) - P) x₁ = x₁ - P x₁ := rfl
      rw [h2, inner_sub_right, hPv1, hx₁self, sub_self]
    have h3 : ((1 : K →L[ℂ] K) - P) x₁ = 0 := su_op_apply_eq_zero h0 h1
    have h4 : x₁ - P x₁ = 0 := h3
    exact (sub_eq_zero.mp h4).symm
  have hQx₂ : Q x₂ = x₂ := by
    have h0 : (0 : K →L[ℂ] K) ≤ 1 - Q := sub_nonneg.mpr hQ1
    have h1 : (⟪x₂, ((1 : K →L[ℂ] K) - Q) x₂⟫ : ℂ) = 0 := by
      have h2 : ((1 : K →L[ℂ] K) - Q) x₂ = x₂ - Q x₂ := rfl
      rw [h2, inner_sub_right, hQv2, hx₂self, sub_self]
    have h3 : ((1 : K →L[ℂ] K) - Q) x₂ = 0 := su_op_apply_eq_zero h0 h1
    have h4 : x₂ - Q x₂ = 0 := h3
    exact (sub_eq_zero.mp h4).symm
  have horth : (⟪x₂, x₁⟫ : ℂ) = 0 := by
    have hsa := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (IsSelfAdjoint.of_nonneg hP0)
    have h : (⟪P x₂, x₁⟫ : ℂ) = ⟪x₂, P x₁⟫ := hsa x₂ x₁
    rw [hPx₂, hPx₁, inner_zero_left] at h
    exact h.symm
  have horth' : (⟪x₁, x₂⟫ : ℂ) = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hPQ : P + Q = (1 : K →L[ℂ] K) := by
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : w = (⟪x₁, w⟫ : ℂ) • x₁ + (⟪x₂, w⟫ : ℂ) • x₂ := by
      have hh : w - ((⟪x₁, w⟫ : ℂ) • x₁ + (⟪x₂, w⟫ : ℂ) • x₂) = 0 := by
        refine hspan _ ?_ ?_
        · rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
            hx₁self, horth', mul_one, mul_zero, add_zero, sub_self]
        · rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
            hx₂self, horth, mul_one, mul_zero, zero_add, sub_self]
      exact sub_eq_zero.mp hh
    have hgoal : (P + Q) w = (⟪x₁, w⟫ : ℂ) • x₁ + (⟪x₂, w⟫ : ℂ) • x₂ := by
      conv_lhs => rw [hw]
      show P ((⟪x₁, w⟫ : ℂ) • x₁ + (⟪x₂, w⟫ : ℂ) • x₂)
        + Q ((⟪x₁, w⟫ : ℂ) • x₁ + (⟪x₂, w⟫ : ℂ) • x₂) = _
      rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hPx₁, hPx₂,
        hQx₁, hQx₂, smul_zero, smul_zero, add_zero, zero_add]
    rw [hgoal]
    show _ = w
    exact hw.symm
  have hFtot : IsTotal F.1 := by
    refine (su_isTotal_iff F.1).mpr ?_
    have h1 : (1 : ULift.{u} ℂ × ULift.{u} ℂ)
        = ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ)
          + ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) := by
      refine Prod.ext ?_ ?_
      · show (1 : ULift.{u} ℂ) = 1 + 0
        rw [add_zero]
      · show (1 : ULift.{u} ℂ) = 0 + 1
        rw [zero_add]
    have h2 : F.1.unop.toNCPMap (1 : ULift.{u} ℂ × ULift.{u} ℂ)
        = (1 : (K →L[ℂ] K) × C) := by
      rw [h1, hFadd, htP, htQ]
      refine Prod.ext ?_ ?_
      · show tP.1 + tQ.1 = (1 : K →L[ℂ] K)
        rw [← hPdef, ← hQdef]
        exact hPQ
      · exact (hCzero _).trans (hCzero _).symm
    exact h2
  -- a total pure map is an iso after a comprehension, hence **surjective**
  obtain ⟨W, ξ, π, q, hξiso, hπ, hFeq⟩ := total_pure_iso_compr F.2 hFtot
  have := hξiso
  have hπsurj := su_compr_surjective hπ
  have hξsurj : Function.Surjective ⇑ξ.unop.toNCPMap := by
    intro y
    refine ⟨(inv ξ).unop.toNCPMap y, ?_⟩
    have h : (ξ ≫ inv ξ).unop.toNCPMap y
        = (𝟙 (suP (suBH K) (suOb C))).unop.toNCPMap y :=
      congrArg (fun mm : suP (suBH K) (suOb C) ⟶ suP (suBH K) (suOb C) =>
        mm.unop.toNCPMap y) (IsIso.hom_inv_id ξ)
    rw [suop_comp_apply ξ (inv ξ) y,
      suop_id_apply (X := suP (suBH K) (suOb C)) y] at h
    exact h
  have hFsurj : ∀ t : (K →L[ℂ] K) × C, ∃ b : ULift.{u} ℂ × ULift.{u} ℂ,
      F.1.unop.toNCPMap b = t := by
    intro t
    obtain ⟨s, hs⟩ := hξsurj t
    obtain ⟨b, hb⟩ := hπsurj s
    refine ⟨b, ?_⟩
    have h : F.1.unop.toNCPMap b = ξ.unop.toNCPMap (π.unop.toNCPMap b) := by
      rw [hFeq]
      exact suop_comp_apply ξ π b
    rw [h, hb, hs]
  -- the contradiction: `|x₁+x₂⟩⟨x₁+x₂|` is not a combination of `P` and `Q`
  obtain ⟨b, hb⟩ := hFsurj ((rk1 (x₁ + x₂), 0) : (K →L[ℂ] K) × C)
  have hb2 : b = b.1.down • ((1, 0) : ULift.{u} ℂ × ULift.{u} ℂ)
      + b.2.down • ((0, 1) : ULift.{u} ℂ × ULift.{u} ℂ) := by
    refine Prod.ext (ULift.ext _ _ ?_) (ULift.ext _ _ ?_)
    · show b.1.down = b.1.down * 1 + b.2.down * 0
      ring
    · show b.2.down = b.1.down * 0 + b.2.down * 1
      ring
  have hR : F.1.unop.toNCPMap b = b.1.down • tP + b.2.down • tQ := by
    conv_lhs => rw [hb2]
    rw [hFadd, hFsmul, hFsmul, htP, htQ]
    rfl
  have hRb : b.1.down • P + b.2.down • Q = rk1 (x₁ + x₂) := by
    rw [hPdef, hQdef]
    exact congrArg Prod.fst (hR.symm.trans hb)
  have happ := congrArg (fun T : K →L[ℂ] K => T x₁) hRb
  simp only [add_apply, smul_apply, hPx₁,
    hQx₁, smul_zero, add_zero, rk1_apply] at happ
  have hinner : (⟪x₁ + x₂, x₁⟫ : ℂ) = 1 := by
    rw [inner_add_left, hx₁self, horth, add_zero]
  rw [hinner, one_smul] at happ
  have hfin := congrArg (fun vv : K => (⟪x₂, vv⟫ : ℂ)) happ
  simp only [inner_smul_right, inner_add_right, horth, hx₂self, mul_zero,
    zero_add] at hfin
  exact zero_ne_one hfin


/-- **224VI at `vNᵒᵖ` on the printed route** (`exc-purec-no-biproduct`,
eff.tex:7189, Exercise\*; solution bsols.tex:3356-3477): `Pure (vNᵒᵖ)` does
**not** have binary coproducts.

This is the printed solution, stage by stage.  Assume `ℂ` and `ℂ` have a
coproduct `𝒜` in `Pure (vNᵒᵖ)`, with coprojections `π₁, π₂` and mediating
map `h` for `id, id`.  Stage (1), the classification of the pure states,
is `su_pure_state_classification`, applied to `h†`: it produces `ℋ`, `𝒞`,
an nmiu-isomorphism `φ : B(ℋ) ⊕ 𝒞 → 𝒜` and `z ∈ ℋ` with
`h†(φ(T,c)) = ⟪z, Tz⟫`; `h†` is unital, because `h† ∘ π₁† = (π₁ ∘ h)† = id`,
so `z` is a unit vector.  Transporting the whole diagram along `φ` — which
is legitimate, `φ` being an isomorphism of `Pure (vNᵒᵖ)` — puts us in
`su_224VI_false`, which runs stages (2)-(5). -/
theorem su_224VI_printed :
    ¬ HasBinaryCoproducts (PureCat (WStarCPSU.{u}ᵒᵖ)) := by
  obtain ⟨d⟩ := su_daggerEffectus.{u}
  intro hbc
  have := hbc
  -- the coproduct diagram and its mediating map for `id, id`
  have hml : (coprod.inl : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      (PureCat.of suI.{u} ⨿ PureCat.of suI.{u})) ≫
      coprod.desc (𝟙 (PureCat.of suI.{u})) (𝟙 (PureCat.of suI.{u}))
      = 𝟙 (PureCat.of suI.{u}) := coprod.inl_desc _ _
  have hmr : (coprod.inr : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
      (PureCat.of suI.{u} ⨿ PureCat.of suI.{u})) ≫
      coprod.desc (𝟙 (PureCat.of suI.{u})) (𝟙 (PureCat.of suI.{u}))
      = 𝟙 (PureCat.of suI.{u}) := coprod.inr_desc _ _
  set A : PureCat (WStarCPSU.{u}ᵒᵖ) :=
    PureCat.of suI.{u} ⨿ PureCat.of suI.{u} with hAdef
  set m₀ : A ⟶ PureCat.of suI.{u} :=
    coprod.desc (𝟙 (PureCat.of suI.{u})) (𝟙 (PureCat.of suI.{u})) with hm₀def
  set dm : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ A :=
    d.daggerCat.dag m₀ with hdmdef
  -- `h†` is unital: `h† ∘ π₁† = (π₁ ∘ h)† = id`
  have hdmid : dm ≫ d.daggerCat.dag
      (coprod.inl : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ A)
      = 𝟙 (PureCat.of suI.{u}) := by
    rw [hdmdef, ← d.daggerCat.dag_comp, hml, d.daggerCat.dag_id]
  have hdm1 : dm.1.unop.toNCPMap (1 : A.base.unop.base.carrier)
      = (1 : ULift.{u} ℂ) := by
    have hval : dm.1 ≫ (d.daggerCat.dag
        (coprod.inl : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ A)).1
        = 𝟙 (suI.{u}) := congrArg Subtype.val hdmid
    have h2 := congrArg
      (fun t : suI.{u} ⟶ suI.{u} => t.unop.toNCPMap (1 : ULift.{u} ℂ)) hval
    rw [suop_comp_apply dm.1 (d.daggerCat.dag
        (coprod.inl : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶ A)).1
        (1 : ULift.{u} ℂ),
      suop_id_apply (X := suI.{u}) (1 : ULift.{u} ℂ)] at h2
    refine le_antisymm dm.1.unop.subunital' ?_
    have hle := ncpsu_mono dm.1.unop ((d.daggerCat.dag
      (coprod.inl : (PureCat.of suI.{u} : PureCat (WStarCPSU.{u}ᵒᵖ)) ⟶
        A)).1.unop.subunital')
    exact le_of_eq_of_le h2.symm hle
  -- stage (1): the classification of the pure state `h†`
  obtain ⟨K, iN, iI, iCo, C, iCS, iPO, iSO, iVN, Φ, y, hΦbij, hΦval⟩ :=
    su_pure_state_classification dm.1 dm.2
  have hΦ1 : Φ (1 : A.base.unop.base.carrier) = 1 := map_one Φ.toStarAlgHom
  have hyy : (⟪y, y⟫ : ℂ) = 1 := by
    have h := hΦval (1 : A.base.unop.base.carrier)
    rw [hdm1, hΦ1] at h
    have h2 : (⟪y, ((1 : (K →L[ℂ] K) × C).1) y⟫ : ℂ) = ⟪y, y⟫ := by
      show (⟪y, (1 : K →L[ℂ] K) y⟫ : ℂ) = _
      rw [show ((1 : K →L[ℂ] K) y) = y from rfl]
    rw [h2] at h
    exact h.symm
  have hyn : ‖y‖ = 1 := by
    have h2 : ((‖y‖ : ℂ)) ^ 2 = 1 := by
      rw [← hyy, inner_self_eq_norm_sq_to_K]
      rfl
    have h3 : (‖y‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h2
    nlinarith [norm_nonneg y]
  -- the isomorphism `φ⁻¹ : 𝒜 → B(ℋ) ⊕ 𝒞` as an isomorphism of `Pure (vNᵒᵖ)`
  obtain ⟨gΦ, hgΦ⟩ := su_exists_ncpsu_of_nmiu Φ
  obtain ⟨gI, hgI1, hgI2⟩ := Theses.B.Dils.exists_ncp_inv Φ hΦbij
  have hgI1' : gI (1 : (K →L[ℂ] K) × C) = 1 := by
    have h := hgI1 (1 : A.base.unop.base.carrier)
    rw [hΦ1] at h
    exact h
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : A.base ⟶ suP (suBH K) (suOb C),
      ∀ a : (K →L[ℂ] K) × C, Ψ.unop.toNCPMap a = gI a :=
    ⟨Quiver.Hom.op ⟨gI, le_of_eq hgI1'⟩, fun _ => rfl⟩
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : suP (suBH K) (suOb C) ⟶ A.base,
      ∀ a : A.base.unop.base.carrier, Ψ'.unop.toNCPMap a = Φ a :=
    ⟨Quiver.Hom.op gΦ, fun a => hgΦ a⟩
  have hΨΨ' : Ψ ≫ Ψ' = 𝟙 A.base := by
    refine suop_hom_ext fun a => ?_
    rw [suop_comp_apply Ψ Ψ' a, hΨ' a, hΨ (Φ a), hgI1 a, suop_id_apply a]
  have hΨ'Ψ : Ψ' ≫ Ψ = 𝟙 (suP (suBH K) (suOb C)) := by
    refine suop_hom_ext fun a => ?_
    rw [suop_comp_apply Ψ' Ψ a, hΨ a, hΨ' (gI a), hgI2 a, suop_id_apply a]
  have hisoΨ : IsIso Ψ := ⟨Ψ', hΨΨ', hΨ'Ψ⟩
  have hisoΨ' : IsIso Ψ' := ⟨Ψ, hΨ'Ψ, hΨΨ'⟩
  have hpΨ : IsPure Ψ := by
    have h := isPure_comp_iso (isPure_id A.base) Ψ
    rwa [Category.id_comp] at h
  have hpΨ' : IsPure Ψ' := by
    have h := isPure_comp_iso (isPure_id (suP (suBH K) (suOb C))) Ψ'
    rwa [Category.id_comp] at h
  obtain ⟨α, hαhom, hαinv⟩ :
      ∃ α : A ≅ PureCat.of (suP (suBH K) (suOb C)),
        α.hom.1 = Ψ ∧ α.inv.1 = Ψ' :=
    ⟨{ hom := ⟨Ψ, hpΨ⟩, inv := ⟨Ψ', hpΨ'⟩,
       hom_inv_id := Subtype.ext hΨΨ', inv_hom_id := Subtype.ext hΨ'Ψ },
      rfl, rfl⟩
  -- the transported diagram
  have hdagm : ∀ a : (K →L[ℂ] K) × C,
      (d.daggerCat.dag (α.inv ≫ m₀)).1.unop.toNCPMap a
        = ULift.up (⟪y, a.1 y⟫ : ℂ) := by
    intro a
    have hinv : d.daggerCat.dag α.inv = α.hom := dagger_of_iso d α.symm
    have hd : d.daggerCat.dag (α.inv ≫ m₀) = dm ≫ α.hom := by
      rw [d.daggerCat.dag_comp, hinv, hdmdef]
    rw [hd]
    have h1 : (dm ≫ α.hom).1.unop.toNCPMap a
        = dm.1.unop.toNCPMap (α.hom.1.unop.toNCPMap a) :=
      suop_comp_apply dm.1 α.hom.1 a
    rw [h1, hαhom, hΨ a]
    refine ULift.ext _ _ ?_
    have h2 := hΦval (gI a)
    rw [hgI2 a] at h2
    exact h2
  -- the swap of `ℂ ⊕ ℂ`, to make the second coprojection pure
  obtain ⟨sw, hsw⟩ : ∃ sw : suP suI.{u} suI.{u} ⟶ suP suI.{u} suI.{u},
      ∀ a : ULift.{u} ℂ × ULift.{u} ℂ, sw.unop.toNCPMap a = (a.2, a.1) :=
    ⟨Quiver.Hom.op (wPairSU (wSndSU (ULift.{u} ℂ) (ULift.{u} ℂ))
      (wFstSU (ULift.{u} ℂ) (ULift.{u} ℂ))), fun _ => rfl⟩
  have hswsw : sw ≫ sw = 𝟙 (suP suI.{u} suI.{u}) := by
    refine suop_hom_ext fun a => ?_
    rw [suop_comp_apply sw sw a, hsw a, hsw ((a.2, a.1) : ULift.{u} ℂ × ULift.{u} ℂ),
      suop_id_apply a]
    rfl
  have hisosw : IsIso sw := ⟨sw, hswsw, hswsw⟩
  have hpsw : IsPure sw := by
    have h := isPure_comp_iso (isPure_id (suP suI.{u} suI.{u})) sw
    rwa [Category.id_comp] at h
  -- everything is in place: apply the five stages
  refine su_224VI_false (K := K) (C := C) d
    (fun p hp => su_minimalProjection_prod hp)
    (fun p hp => su_minimalProjection_rk1 hp)
    ⟨suPq (suBH K) (suOb C), su_isPure_suPq _ _⟩
    (fun T => suPq_apply (suBH K) (suOb C) T)
    ⟨suPinl (suBH K) (suOb C), su_isPure_suPinl _ _⟩ (fun a => rfl)
    (Subtype.ext (su_dagger_suPq d (suBH K) (suOb C)))
    ⟨suPinl suI.{u} suI.{u}, su_isPure_suPinl _ _⟩
    ⟨suPinl suI.{u} suI.{u} ≫ sw, upm_closed_pure (su_isPure_suPinl _ _) hpsw⟩
    (fun a => rfl) (fun a => ?_)
    (coprod.inl ≫ α.hom) (coprod.inr ≫ α.hom) (α.inv ≫ m₀) ?_ ?_ ?_ ?_ hyn hdagm
  · -- the second coprojection of `ℂ ⊕ ℂ`, through the swap
    have h1 : (suPinl suI.{u} suI.{u} ≫ sw).unop.toNCPMap a
        = (suPinl suI.{u} suI.{u}).unop.toNCPMap (sw.unop.toNCPMap a) :=
      suop_comp_apply (suPinl suI.{u} suI.{u}) sw a
    rw [h1, hsw a]
    rfl
  · -- `π₁ ∘ h = id`
    rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id, Category.id_comp]
    exact hml
  · -- `π₂ ∘ h = id`
    rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id, Category.id_comp]
    exact hmr
  · -- uniqueness of mediating maps
    intro W u v h1 h2
    refine (cancel_epi α.hom).mp ?_
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, ← Category.assoc]
      exact h1
    · rw [← Category.assoc, ← Category.assoc]
      exact h2
  · -- existence of mediating maps
    intro W a b
    refine ⟨α.inv ≫ coprod.desc a b, ?_, ?_⟩
    · rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id, Category.id_comp,
        coprod.inl_desc]
    · rw [Category.assoc, ← Category.assoc α.hom, α.hom_inv_id, Category.id_comp,
        coprod.inr_desc]


end Printed

end PrintedRoute224VI

/-! #### The short route, kept alongside

`su_exc_purec_no_biproduct_short` below uses none of the above: no
classification, no dagger, no minimal projection. -/

/-- A substate `f : ℂ ⟶ X` of `vN_cpsuᵒᵖ`, i.e. an ncpsu-map
`X.unop → ℂ`, as a linear functional. -/
private noncomputable def suFun {X : WStarCPSU.{u}ᵒᵖ} (f : suI.{u} ⟶ X) :
    X.unop.base.carrier →ₗ[ℂ] ℂ where
  toFun x := (f.unop.toNCPMap x).down
  map_add' x y := by rw [ncp_add_apply]; rfl
  map_smul' c x := by rw [ncp_smul_apply]; rfl

private theorem suFun_apply {X : WStarCPSU.{u}ᵒᵖ} (f : suI.{u} ⟶ X)
    (x : X.unop.base.carrier) : suFun f x = (f.unop.toNCPMap x).down := rfl

private theorem suFun_pos {X : WStarCPSU.{u}ᵒᵖ} (f : suI.{u} ⟶ X) :
    IsPositiveMap (suFun f) := by
  intro x hx
  have h := ncpsu_mono f.unop hx
  rw [ncp_zero_apply] at h
  exact h

/-- **The short route**, kept for the record: `Pure (vNᵒᵖ)` has no binary
coproducts, by an argument that uses none of the printed solution.  Both
coprojections are *states* fixing `a₀ = ĝ₀(1)`, so they agree on
`√a₀ a₁ √a₀`, which lies in the range of the mediating map `ĝ₀`; that gives
`1 = π₁(a₁) = π₂(a₁) = 0`.  `su_exc_purec_no_biproduct` below is the same
statement on the print's own route. -/
theorem su_exc_purec_no_biproduct_short :
    ¬ HasBinaryCoproducts (PureCat (WStarCPSU.{u}ᵒᵖ)) := by
  intro hbc
  haveI := hbc
  set IP : PureCat (WStarCPSU.{u}ᵒᵖ) := PureCat.of suI.{u} with hIP
  set A : PureCat (WStarCPSU.{u}ᵒᵖ) := IP ⨿ IP with hAdef
  set z0 : IP ⟶ IP := ⟨(0 : suI.{u} ⟶ suI.{u}), isPure_zero⟩ with hz0
  set g₀ : A ⟶ IP := coprod.desc (𝟙 IP) (𝟙 IP) with hg0
  set g₁ : A ⟶ IP := coprod.desc (𝟙 IP) z0 with hg1
  set i₁ : IP ⟶ A := coprod.inl with hi1
  set i₂ : IP ⟶ A := coprod.inr with hi2
  have e10 : i₁ ≫ g₀ = 𝟙 IP := coprod.inl_desc _ _
  have e20 : i₂ ≫ g₀ = 𝟙 IP := coprod.inr_desc _ _
  have e11 : i₁ ≫ g₁ = 𝟙 IP := coprod.inl_desc _ _
  have e21 : i₂ ≫ g₁ = z0 := coprod.inr_desc _ _
  -- the coprojections are sections of the mediating maps
  have key : ∀ (g : A ⟶ IP) (i : IP ⟶ A), i ≫ g = 𝟙 IP →
      ∀ z : (suI.{u}).unop.base.carrier,
        i.1.unop.toNCPMap (g.1.unop.toNCPMap z) = z := by
    intro g i h z
    have h2 : i.1 ≫ g.1 = 𝟙 (IP.base) := congrArg (fun m : IP ⟶ IP => m.1) h
    have h3 : (i.1 ≫ g.1).unop.toNCPMap z = (𝟙 (IP.base)).unop.toNCPMap z :=
      congrArg (fun m : IP.base ⟶ IP.base => m.unop.toNCPMap z) h2
    rw [suop_comp_apply, suop_id_apply] at h3
    exact h3
  have k10 := key g₀ i₁ e10
  have k20 := key g₀ i₂ e20
  have k11 := key g₁ i₁ e11
  have k21 : ∀ z : (suI.{u}).unop.base.carrier,
      i₂.1.unop.toNCPMap (g₁.1.unop.toNCPMap z) = 0 := by
    intro z
    have h2 : i₂.1 ≫ g₁.1 = (0 : suI.{u} ⟶ suI.{u}) :=
      congrArg (fun m : IP ⟶ IP => m.1) e21
    have h3 : (i₂.1 ≫ g₁.1).unop.toNCPMap z
        = (0 : suI.{u} ⟶ suI.{u}).unop.toNCPMap z :=
      congrArg (fun m : IP.base ⟶ IP.base => m.unop.toNCPMap z) h2
    rw [suop_comp_apply] at h3
    exact h3
  -- the two effects `a₀` and `a₁`
  set a₀ : A.base.unop.base.carrier := g₀.1.unop.toNCPMap 1 with ha0def
  set a₁ : A.base.unop.base.carrier := g₁.1.unop.toNCPMap 1 with ha1def
  have ha00 : 0 ≤ a₀ := by
    have h := ncpsu_mono g₀.1.unop
      (zero_le_one (α := (suI.{u}).unop.base.carrier))
    rw [ncp_zero_apply] at h
    rwa [ha0def]
  have ha01 : a₀ ≤ 1 := by rw [ha0def]; exact g₀.1.unop.subunital'
  have ha10 : 0 ≤ a₁ := by
    have h := ncpsu_mono g₁.1.unop
      (zero_le_one (α := (suI.{u}).unop.base.carrier))
    rw [ncp_zero_apply] at h
    rwa [ha1def]
  have ha11 : a₁ ≤ 1 := by rw [ha1def]; exact g₁.1.unop.subunital'
  -- both coprojections are states fixing `a₀`
  have hstate : ∀ (i : IP ⟶ A),
      (∀ z : (suI.{u}).unop.base.carrier,
        i.1.unop.toNCPMap (g₀.1.unop.toNCPMap z) = z) →
      suFun i.1 (CFC.sqrt a₀ * a₁ * CFC.sqrt a₀) = suFun i.1 a₁ := by
    intro i hi
    have hfix : i.1.unop.toNCPMap a₀ = 1 := by rw [ha0def]; exact hi 1
    have hone : i.1.unop.toNCPMap (1 : A.base.unop.base.carrier) = 1 := by
      refine le_antisymm i.1.unop.subunital' ?_
      have h2 : i.1.unop.toNCPMap a₀ ≤ i.1.unop.toNCPMap 1 :=
        ncpsu_mono i.1.unop ha01
      rwa [hfix] at h2
    refine su_state_sqrtConj (suFun i.1) (suFun_pos i.1) ?_ ha00 ha01 ?_ a₁
    · rw [suFun_apply, hone]; rfl
    · rw [suFun_apply, hfix]; rfl
  -- `√a₀ a₁ √a₀` lies in the range of the mediating map `ĝ₀`
  obtain ⟨w, hw⟩ := su_pure_range (f := g₀.1) g₀.2 ha10 ha11
  rw [← ha0def] at hw
  have hval : ∀ (i : IP ⟶ A),
      (∀ z : (suI.{u}).unop.base.carrier,
        i.1.unop.toNCPMap (g₀.1.unop.toNCPMap z) = z) →
      suFun i.1 (CFC.sqrt a₀ * a₁ * CFC.sqrt a₀) = w.down := by
    intro i hi
    rw [suFun_apply, ← hw, hi w]
  -- the contradiction
  have h1 : suFun i₁.1 a₁ = 1 := by
    have h : i₁.1.unop.toNCPMap a₁ = 1 := by rw [ha1def]; exact k11 1
    rw [suFun_apply, h]; rfl
  have h2 : suFun i₂.1 a₁ = 0 := by
    have h : i₂.1.unop.toNCPMap a₁ = 0 := by rw [ha1def]; exact k21 1
    rw [suFun_apply, h]; rfl
  have e1 : (1 : ℂ) = w.down := by rw [← h1, ← hstate i₁ k10, hval i₁ k10]
  have e2 : (0 : ℂ) = w.down := by rw [← h2, ← hstate i₂ k20, hval i₂ k20]
  exact one_ne_zero (e1.trans e2.symm)

/-- **224VI at `vNᵒᵖ`** (`exc-purec-no-biproduct`, eff.tex:7189, Exercise\*;
solution bsols.tex:3358): `Pure (vNᵒᵖ)` does **not** have binary
coproducts — already `ℂ` and `ℂ` have none.

This is the printed solution, all six stages: see `su_224VI_printed`, of
which this is a restatement, and the section note above it. -/
theorem su_exc_purec_no_biproduct :
    ¬ HasBinaryCoproducts (PureCat (WStarCPSU.{u}ᵒᵖ)) := su_224VI_printed

end PureCoequalizer

end IUnique

/-! ## `CvNᵒᵖ` in partial form, and the `CvNᵒᵖ` clause of 206III

**206III** (eff.tex:4460, Examples) asserts that `vNᵒᵖ`, `CvNᵒᵖ`, `EJAᵒᵖ`
and `SET` are all ⋄-effectuses.  `effectus_cvn` above did the *total*-form
restriction to the commutative algebras (189aI, second sentence); a
⋄-effectus, however, lives in the **partial** form, so the whole of 180VII
has to be restricted as well.  That is what this section does, ending in
`su_diamondEffectus_cvn`.

No von Neumann algebra theory is redone.  The inclusion
`CvNᵒᵖ ⥤ vNᵒᵖ` is a bijection on each hom-set — `cmap`/`cmk` below, mutually
inverse by `rfl` — so:

* the hom-PCM, the six finPAC axioms and the effect structure of 180VII are
  **pulled back** along it.  The effect object `ℂᵤ`, the trivial algebra
  and a product of commutative algebras are commutative, so the effect
  object, the initial object and the binary coproducts of `vN_cpsuᵒᵖ` all
  stay inside the subcategory.  (Only `compatible_sum` needs a moment's
  care: the *chosen* coproduct `Y + Y` of the subcategory is merely
  isomorphic to the product algebra, so the ambient axiom is read at the
  transported cofan, `perp_comp_comp`.)
* the universal properties of a quotient, of a comprehension and of an
  image quantify over *objects of the ambient category*; restricting them
  to the subcategory only makes them weaker.  So an ambient
  quotient/comprehension whose new object happens to be commutative is at
  once one of the subcategory, and the whole mathematical content is:
  **the objects the ⋄-structure of `vN_cpsuᵒᵖ` adds are corners `p𝒜p`, and
  a corner of a commutative algebra is commutative**, its multiplication
  being that of `𝒜`.  That is the last conjunct of `su_exists_corner` and
  of `su_exists_filter`.  Images add no object at all.
* sharpness is the one notion that does *not* restrict for free, being an
  existential over objects of the subcategory.  `cvnsu_isSharp_cpred` pushes
  a sharp predicate of `CvNᵒᵖ` forward to a sharp predicate of `vNᵒᵖ`
  (images are unique), `su_orth_sharp` complements it there, and the
  *commutative* standard corner of `su_exists_corner` brings it back — using
  **203XII** `img_of_compr`, `im π_s = s` for sharp `s`, to see that a
  comprehension for a sharp predicate has that predicate as its image. -/

section CvNPartial

open Theses.A.CStar
open scoped ComplexOrder ComplexStarModule

attribute [local instance] suHasFiniteCoproducts suPCM suFinPAC
  suEffectusPartialForm su_hasQuotients su_hasComprehension su_hasImages

/-- The compatible-sum axiom of a finPAC read through an arbitrary map into
the coproduct: if `d₁ = φ ∘ ▷₁` and `d₂ = φ ∘ ▷₂` then `b ∘ d₁ ⊥ b ∘ d₂`.
(Used for `CvNᵒᵖ`, whose *chosen* coproduct is only isomorphic to the
product algebra.) -/
theorem perp_comp_comp {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] {Y W Z : C} (φ : W ⟶ Y ⨿ Y)
    {d₁ d₂ : W ⟶ Y} (h₁ : d₁ = φ ≫ pproj₁ Y Y) (h₂ : d₂ = φ ≫ pproj₂ Y Y)
    (b : Z ⟶ W) : Perp (b ≫ d₁) (b ≫ d₂) := by
  subst h₁
  subst h₂
  have h := FinPAC.compatible_sum (b ≫ φ)
  rwa [Category.assoc, Category.assoc] at h

/-- The concrete binary coproduct of `vN_cpsuᵒᵖ` is jointly epic: the two
coprojections of `suHP`, in the shape `rw` can use. -/
theorem suP_hom_ext {X Y Z : WStarCPSU.{u}ᵒᵖ} {f g : suP X Y ⟶ Z}
    (h₁ : suPinl X Y ≫ f = suPinl X Y ≫ g)
    (h₂ : suPinr X Y ≫ f = suPinr X Y ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (suHP X Y) h₁ h₂

/-! ### The category `CvN_cpsu` and the hom-bijection -/

/-- Commutativity of the carrier, as a property of the objects of
`vN_cpsu`: the ncpsu-map counterpart of `IsCommWStar`. -/
def IsCommWStarCPSU : ObjectProperty WStarCPSU.{u} :=
  fun A => ∀ x y : A.base.carrier, x * y = y * x

/-- **`CvN_cpsu`**: the full subcategory of `vN_cpsu` spanned by the
commutative von Neumann algebras (the morphisms are still all ncpsu-maps),
so that `CWStarCPSU.{u}ᵒᵖ` is the `CvNᵒᵖ` of 206III in partial form. -/
abbrev CWStarCPSU : Type (u + 1) := IsCommWStarCPSU.{u}.FullSubcategory

theorem cvn_mul_comm (X : CWStarCPSU.{u}) (x y : X.obj.base.carrier) :
    x * y = y * x := X.property x y

/-- The object of `vN_cpsuᵒᵖ` underlying an object of `CvNᵒᵖ`. -/
abbrev cin (X : CWStarCPSU.{u}ᵒᵖ) : WStarCPSU.{u}ᵒᵖ := Opposite.op X.unop.obj

/-- The morphism of `vN_cpsuᵒᵖ` underlying a morphism of `CvNᵒᵖ`: the action
of the (fully faithful) inclusion on hom-sets. -/
noncomputable def cmap {X Y : CWStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) : cin X ⟶ cin Y :=
  Quiver.Hom.op f.unop.hom

/-- The inverse of `cmap`: every morphism of `vN_cpsuᵒᵖ` between commutative
algebras is a morphism of `CvNᵒᵖ` (the subcategory is *full*). -/
noncomputable def cmk {X Y : CWStarCPSU.{u}ᵒᵖ} (g : cin X ⟶ cin Y) : X ⟶ Y :=
  Quiver.Hom.op (InducedCategory.homMk g.unop)

@[simp] theorem cmap_cmk {X Y : CWStarCPSU.{u}ᵒᵖ} (g : cin X ⟶ cin Y) :
    cmap (cmk g) = g := rfl

@[simp] theorem cmk_cmap {X Y : CWStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    cmk (cmap f) = f := rfl

theorem cmap_injective {X Y : CWStarCPSU.{u}ᵒᵖ} {f g : X ⟶ Y}
    (h : cmap f = cmap g) : f = g := by
  rw [← cmk_cmap f, ← cmk_cmap g, h]

@[simp] theorem cmap_comp {X Y Z : CWStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cmap (f ≫ g) = cmap f ≫ cmap g := rfl

@[simp] theorem cmap_id (X : CWStarCPSU.{u}ᵒᵖ) : cmap (𝟙 X) = 𝟙 (cin X) := rfl

/-! ### The hom-PCM -/

/-- **The hom-PCM of `CvNᵒᵖ`** (180VII.1): pulled back from `vN_cpsuᵒᵖ`
along the bijection `cmap`, so that — exactly as in `suPCM` — `f ⊥ g` iff
`f(1) + g(1) ≤ 1` and `f ⋁ g = f + g`. -/
noncomputable def cvnsuPCM (X Y : CWStarCPSU.{u}ᵒᵖ) : PCM (X ⟶ Y) where
  zero := cmk 0
  Perp f g := Perp (cmap f) (cmap g)
  ovee f g h := cmk (ovee (cmap f) (cmap g) h)
  perp_comm h := PCM.perp_comm h
  ovee_comm h := congrArg cmk (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := congrArg cmk (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp (cmap a)
  zero_ovee a := congrArg cmk (PCM.zero_ovee (cmap a))

attribute [local instance] cvnsuPCM

@[simp] theorem cmap_zero {X Y : CWStarCPSU.{u}ᵒᵖ} :
    cmap (0 : X ⟶ Y) = 0 := rfl

@[simp] theorem cmap_ovee {X Y : CWStarCPSU.{u}ᵒᵖ} (f g : X ⟶ Y)
    (h : Perp f g) : cmap (ovee f g h) = ovee (cmap f) (cmap g) h := rfl

/-- The algebraic order `≼` of the hom-PCM of `CvNᵒᵖ` is the ambient one. -/
theorem cvnsu_le_iff {X Y : CWStarCPSU.{u}ᵒᵖ} (f g : X ⟶ Y) :
    f ≼ g ↔ cmap f ≼ cmap g := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨cmap c, hc, rfl⟩
  · rintro ⟨c, hc, hcg⟩
    exact ⟨cmk c, hc, cmap_injective hcg⟩

/-! ### Finite coproducts -/

/-- The trivial algebra as an object of `CvN_cpsu`: it is commutative. -/
noncomputable abbrev cvnsuTriv : CWStarCPSU.{u} :=
  ⟨WStarCPSU.of (WStar.of PUnit.{u + 1}),
    fun _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _⟩

/-- The trivial algebra is final in `CvN_cpsu`, hence initial in
`CvNᵒᵖ` (uniqueness in the subcategory is uniqueness in `vN_cpsu`). -/
noncomputable def cvnsuTrivIsTerminal : IsTerminal (cvnsuTriv.{u}) :=
  IsTerminal.ofUniqueHom
    (fun X => InducedCategory.homMk (wTrivSU X.obj.base.carrier))
    (fun _ _ => InducedCategory.hom_ext
      (ncpsu_ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _))

/-- The product algebra as an object of `CvNᵒᵖ`: the binary coproduct. -/
noncomputable abbrev cvnsuP (X Y : CWStarCPSU.{u}ᵒᵖ) : CWStarCPSU.{u}ᵒᵖ :=
  Opposite.op ⟨WStarCPSU.of (WStar.of
      (X.unop.obj.base.carrier × Y.unop.obj.base.carrier)),
    fun x y => Prod.ext (cvn_mul_comm X.unop x.1 y.1)
      (cvn_mul_comm Y.unop x.2 y.2)⟩

/-- The first coprojection of `CvNᵒᵖ`. -/
noncomputable def cvnsuPinl (X Y : CWStarCPSU.{u}ᵒᵖ) : X ⟶ cvnsuP X Y :=
  cmk (suPinl (cin X) (cin Y))

/-- The second coprojection of `CvNᵒᵖ`. -/
noncomputable def cvnsuPinr (X Y : CWStarCPSU.{u}ᵒᵖ) : Y ⟶ cvnsuP X Y :=
  cmk (suPinr (cin X) (cin Y))

@[simp] theorem cmap_cvnsuPinl (X Y : CWStarCPSU.{u}ᵒᵖ) :
    cmap (cvnsuPinl X Y) = suPinl (cin X) (cin Y) := rfl

@[simp] theorem cmap_cvnsuPinr (X Y : CWStarCPSU.{u}ᵒᵖ) :
    cmap (cvnsuPinr X Y) = suPinr (cin X) (cin Y) := rfl

/-- The product algebra is the binary coproduct of `CvNᵒᵖ`: `cmap` is a
bijection on hom-sets, so `suHP` transports. -/
noncomputable def cvnsuHP (X Y : CWStarCPSU.{u}ᵒᵖ) :
    IsColimit (BinaryCofan.mk (cvnsuPinl X Y) (cvnsuPinr X Y)) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} u v => cmk (suPdesc (cmap u) (cmap v)))
    (fun {_} u v => cmap_injective (suPinl_desc (cmap u) (cmap v)))
    (fun {_} u v => cmap_injective (suPinr_desc (cmap u) (cmap v)))
    (fun {_} u v m h₁ h₂ => by
      refine cmap_injective ?_
      refine suP_hom_ext (X := cin X) (Y := cin Y) ?_ ?_
      · show suPinl (cin X) (cin Y) ≫ cmap m
            = suPinl (cin X) (cin Y) ≫ suPdesc (cmap u) (cmap v)
        rw [suPinl_desc]
        exact congrArg cmap h₁
      · show suPinr (cin X) (cin Y) ≫ cmap m
            = suPinr (cin X) (cin Y) ≫ suPdesc (cmap u) (cmap v)
        rw [suPinr_desc]
        exact congrArg cmap h₂)

/-- Finite coproducts of `CvNᵒᵖ`. -/
theorem cvnsuHasFiniteCoproducts : HasFiniteCoproducts (CWStarCPSU.{u}ᵒᵖ) :=
  letI : HasInitial (CWStarCPSU.{u}ᵒᵖ) :=
    (IsTerminal.op (CWStarCPSU.{u}) cvnsuTrivIsTerminal).hasInitial
  letI : ∀ X Y : CWStarCPSU.{u}ᵒᵖ, HasColimit (pair X Y) := fun X Y =>
    HasColimit.mk ⟨_, cvnsuHP X Y⟩
  letI : HasBinaryCoproducts (CWStarCPSU.{u}ᵒᵖ) :=
    hasBinaryCoproducts_of_hasColimit_pair _
  hasFiniteCoproducts_of_has_binary_and_initial

attribute [local instance] cvnsuHasFiniteCoproducts

/-! ### The finPAC axioms -/

/-- **`CvNᵒᵖ` is a finPAC** (180VII.1).  Five of the six axioms are the
axioms of `suFinPAC` read along the hom-bijection.  `compatible_sum` is the
sixth: the chosen coproduct `Y + Y` of `CvNᵒᵖ` is only *isomorphic* to the
product algebra, so the two partial projectors are first transported to the
product algebra (`h₁`, `h₂`) and the ambient axiom is then read through the
mediating map `[κ₁, κ₂]` by `perp_comp_comp`. -/
theorem cvnsuFinPAC : FinPAC (CWStarCPSU.{u}ᵒᵖ) where
  comp_ovee := fun h k => by
    obtain ⟨h', hk⟩ := FinPAC.comp_ovee (C := WStarCPSU.{u}ᵒᵖ) h (cmap k)
    exact ⟨h', cmap_injective hk⟩
  ovee_comp := fun h k => by
    obtain ⟨h', hk⟩ := FinPAC.ovee_comp (C := WStarCPSU.{u}ᵒᵖ) h (cmap k)
    exact ⟨h', cmap_injective hk⟩
  comp_zero := fun f => cmap_injective (FinPAC.comp_zero (cmap f))
  zero_comp := fun f => cmap_injective (FinPAC.zero_comp (cmap f))
  compatible_sum := fun {_ Y} b => by
    let e : (Y ⨿ Y) ≅ cvnsuP Y Y :=
      (coprodIsCoprod Y Y).coconePointUniqueUpToIso (cvnsuHP Y Y)
    have hl : (coprod.inl : Y ⟶ Y ⨿ Y) ≫ e.hom = cvnsuPinl Y Y :=
      (coprodIsCoprod Y Y).comp_coconePointUniqueUpToIso_hom (cvnsuHP Y Y)
        ⟨WalkingPair.left⟩
    have hr : (coprod.inr : Y ⟶ Y ⨿ Y) ≫ e.hom = cvnsuPinr Y Y :=
      (coprodIsCoprod Y Y).comp_coconePointUniqueUpToIso_hom (cvnsuHP Y Y)
        ⟨WalkingPair.right⟩
    have h₁ : pproj₁ Y Y
        = e.hom ≫ cmk (suPdesc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y)) := by
      refine coprod.hom_ext ?_ ?_
      · rw [show (pproj₁ Y Y) = coprod.desc (𝟙 Y) 0 from rfl, coprod.inl_desc,
          ← Category.assoc, hl]
        refine (cmap_injective ?_).symm
        exact suPinl_desc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y)
      · rw [show (pproj₁ Y Y) = coprod.desc (𝟙 Y) 0 from rfl, coprod.inr_desc,
          ← Category.assoc, hr]
        refine (cmap_injective ?_).symm
        exact suPinr_desc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y)
    have h₂ : pproj₂ Y Y
        = e.hom ≫ cmk (suPdesc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y))) := by
      refine coprod.hom_ext ?_ ?_
      · rw [show (pproj₂ Y Y) = coprod.desc 0 (𝟙 Y) from rfl, coprod.inl_desc,
          ← Category.assoc, hl]
        refine (cmap_injective ?_).symm
        exact suPinl_desc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y))
      · rw [show (pproj₂ Y Y) = coprod.desc 0 (𝟙 Y) from rfl, coprod.inr_desc,
          ← Category.assoc, hr]
        refine (cmap_injective ?_).symm
        exact suPinr_desc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y))
    have hφ₁ : suPdesc (coprod.inl : cin Y ⟶ cin Y ⨿ cin Y)
          (coprod.inr : cin Y ⟶ cin Y ⨿ cin Y) ≫ pproj₁ (cin Y) (cin Y)
        = suPdesc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y) := by
      refine suP_hom_ext (X := cin Y) (Y := cin Y) ?_ ?_
      · rw [← Category.assoc, suPinl_desc, suPinl_desc,
          show (pproj₁ (cin Y) (cin Y)) = coprod.desc (𝟙 (cin Y)) 0 from rfl,
          coprod.inl_desc]
      · rw [← Category.assoc, suPinr_desc, suPinr_desc,
          show (pproj₁ (cin Y) (cin Y)) = coprod.desc (𝟙 (cin Y)) 0 from rfl,
          coprod.inr_desc]
    have hφ₂ : suPdesc (coprod.inl : cin Y ⟶ cin Y ⨿ cin Y)
          (coprod.inr : cin Y ⟶ cin Y ⨿ cin Y) ≫ pproj₂ (cin Y) (cin Y)
        = suPdesc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y)) := by
      refine suP_hom_ext (X := cin Y) (Y := cin Y) ?_ ?_
      · rw [← Category.assoc, suPinl_desc, suPinl_desc,
          show (pproj₂ (cin Y) (cin Y)) = coprod.desc 0 (𝟙 (cin Y)) from rfl,
          coprod.inl_desc]
      · rw [← Category.assoc, suPinr_desc, suPinr_desc,
          show (pproj₂ (cin Y) (cin Y)) = coprod.desc 0 (𝟙 (cin Y)) from rfl,
          coprod.inr_desc]
    have key : Perp (cmap (b ≫ e.hom) ≫ suPdesc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y))
        (cmap (b ≫ e.hom) ≫ suPdesc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y))) :=
      perp_comp_comp _ hφ₁.symm hφ₂.symm _
    have hE₁ : cmap (b ≫ pproj₁ Y Y)
        = cmap (b ≫ e.hom) ≫ suPdesc (𝟙 (cin Y)) (0 : cin Y ⟶ cin Y) := by
      rw [h₁, ← Category.assoc, cmap_comp, cmap_cmk]
    have hE₂ : cmap (b ≫ pproj₂ Y Y)
        = cmap (b ≫ e.hom) ≫ suPdesc (0 : cin Y ⟶ cin Y) (𝟙 (cin Y)) := by
      rw [h₂, ← Category.assoc, cmap_comp, cmap_cmk]
    show Perp (cmap (b ≫ pproj₁ Y Y)) (cmap (b ≫ pproj₂ Y Y))
    rw [hE₁, hE₂]
    exact key
  untying := fun {_ Y f g} h => by
    have h' : Perp ((cmap f) ≫ (coprod.inl : cin Y ⟶ cin Y ⨿ cin Y))
        ((cmap g) ≫ (coprod.inr : cin Y ⟶ cin Y ⨿ cin Y)) :=
      FinPAC.untying (C := WStarCPSU.{u}ᵒᵖ) h
    obtain ⟨h'', -⟩ := FinPAC.comp_ovee h'
      (coprod.desc (cmap (coprod.inl : Y ⟶ Y ⨿ Y))
        (cmap (coprod.inr : Y ⟶ Y ⨿ Y)))
    rw [Category.assoc, Category.assoc, coprod.inl_desc, coprod.inr_desc] at h''
    exact h''

attribute [local instance] cvnsuFinPAC

/-! ### The effects -/

/-- The scalars `ℂᵤ` as an object of `CvN_cpsu`: the effect object of
`CvNᵒᵖ`, and commutative. -/
noncomputable abbrev cvnsuI : CWStarCPSU.{u}ᵒᵖ :=
  Opposite.op ⟨WStarCPSU.of (WStar.of (ULift.{u} ℂ)),
    fun x y => Theses.A.VN.CU.down_injective (mul_comm x.down y.down)⟩

/-- **The effect structure of `CvNᵒᵖ`** (180VII.2): the effect object is
the (commutative) algebra of scalars, and truth, orthocomplement and the
five axioms are read off `suEffectusPartialForm` along `cmap`. -/
noncomputable def cvnsuEffectusPartialForm :
    EffectusPartialForm (CWStarCPSU.{u}ᵒᵖ) where
  I := cvnsuI
  one X := cmk (suOne (cin X))
  orth p := cmk (EffectusPartialForm.orth (C := WStarCPSU.{u}ᵒᵖ) (cmap p))
  perp_orth := fun p =>
    EffectusPartialForm.perp_orth (C := WStarCPSU.{u}ᵒᵖ) (cmap p)
  ovee_orth := fun p =>
    congrArg cmk (EffectusPartialForm.ovee_orth (C := WStarCPSU.{u}ᵒᵖ) (cmap p))
  orth_unique := fun h heq =>
    cmap_injective (EffectusPartialForm.orth_unique (C := WStarCPSU.{u}ᵒᵖ) h
      (congrArg cmap heq))
  eq_zero_of_perp_one := fun h =>
    cmap_injective
      (EffectusPartialForm.eq_zero_of_perp_one (C := WStarCPSU.{u}ᵒᵖ) h)
  perp_of_one_perp := fun h =>
    EffectusPartialForm.perp_of_one_perp (C := WStarCPSU.{u}ᵒᵖ) h
  eq_zero_of_one_zero := fun h =>
    cmap_injective (EffectusPartialForm.eq_zero_of_one_zero
      (C := WStarCPSU.{u}ᵒᵖ) (congrArg cmap h))

attribute [local instance] cvnsuEffectusPartialForm

/-- A predicate of `CvNᵒᵖ`, read as a predicate of `vN_cpsuᵒᵖ`: the same
morphism, because the effect object of `CvNᵒᵖ` *is* the effect object `ℂᵤ`
of `vN_cpsuᵒᵖ`. -/
noncomputable def cpred {X : CWStarCPSU.{u}ᵒᵖ} (p : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)) :
    cin X ⟶ effObj (WStarCPSU.{u}ᵒᵖ) := cmap p

theorem cpred_injective {X : CWStarCPSU.{u}ᵒᵖ}
    {p q : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)} (h : cpred p = cpred q) : p = q :=
  cmap_injective h

theorem cpred_le_iff {X : CWStarCPSU.{u}ᵒᵖ}
    (p q : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)) : p ≼ q ↔ cpred p ≼ cpred q :=
  cvnsu_le_iff p q

/-! ### Quotients, comprehension, images and sharpness -/

/-- **202IV at `CvNᵒᵖ`**: `CvNᵒᵖ` has images.  An image adds no object, and
the universal property of `im f` in the subcategory quantifies over fewer
predicates than in `vN_cpsuᵒᵖ`, so the ambient image *is* the image. -/
theorem cvnsuHasImages : HasImages (CWStarCPSU.{u}ᵒᵖ) where
  im {_ Y} f := by
    obtain ⟨q, hq⟩ := HasImages.im (C := WStarCPSU.{u}ᵒᵖ) (cmap f)
    refine ⟨cmk q, cpred_injective hq.1, ?_⟩
    intro r hr
    exact (cpred_le_iff _ _).mpr (hq.2 (cpred r) (congrArg cpred hr))

/-- **197IV at `CvNᵒᵖ`**: `CvNᵒᵖ` has quotients.  The quotient of a
commutative `𝒜` by an effect `a` is the standard filter onto the corner
`⌈aᗮ⌉𝒜⌈aᗮ⌉`, which is commutative (`su_exists_filter`); its universal
property restricts to the subcategory. -/
theorem cvnsuHasQuotients : HasQuotients (CWStarCPSU.{u}ᵒᵖ) where
  quot {X} p := by
    obtain ⟨Q, ξ, hξ, hQ⟩ := su_exists_filter (cpred p)
    refine ⟨Opposite.op ⟨Q.unop, hQ (cvn_mul_comm X.unop)⟩, cmk ξ,
      (cpred_le_iff _ _).mpr hξ.1, ?_⟩
    intro Y f hf
    obtain ⟨f', hf', huniq⟩ := hξ.2 (cmap f) ((cpred_le_iff _ _).mp hf)
    exact ⟨cmk f', cmap_injective hf',
      fun k hk => cmap_injective (huniq (cmap k) (congrArg cmap hk))⟩

/-- **199V at `CvNᵒᵖ`**: `CvNᵒᵖ` has comprehension.  A comprehension for an
effect `a` of a commutative `𝒜` is the standard corner `⌊a⌋𝒜⌊a⌋`, which is
commutative (`su_exists_corner`); its universal property restricts to the
subcategory. -/
theorem cvnsuHasComprehension : HasComprehension (CWStarCPSU.{u}ᵒᵖ) where
  compr {X} p := by
    obtain ⟨W, π, hπ, -, -, hW⟩ := su_exists_corner (cpred p)
    refine ⟨Opposite.op ⟨W.unop, hW (cvn_mul_comm X.unop)⟩, cmk π,
      cpred_injective hπ.1, ?_⟩
    intro Z g hg
    obtain ⟨g', hg', huniq⟩ := hπ.2 (cmap g) (congrArg cpred hg)
    exact ⟨cmk g', cmap_injective hg',
      fun k hk => cmap_injective (huniq (cmap k) (congrArg cmap hk))⟩

/-- A sharp predicate of `CvNᵒᵖ` is sharp in `vN_cpsuᵒᵖ`: the witness `f` has
an ambient image, the two minimality clauses squeeze it against `s`, and
images are unique. -/
theorem cvnsu_isSharp_cpred {X : CWStarCPSU.{u}ᵒᵖ}
    {s : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)} (hs : IsSharp s) :
    IsSharp (cpred s) := by
  obtain ⟨Y, f, hf⟩ := hs
  obtain ⟨q, hq⟩ := HasImages.im (C := WStarCPSU.{u}ᵒᵖ) (cmap f)
  have h1 : q ≼ cpred s := hq.2 (cpred s) (congrArg cpred hf.1)
  have h2 : cpred s ≼ q :=
    (cpred_le_iff _ _).mp (hf.2 (cmk q) (cpred_injective hq.1))
  have hsq : cpred s = q := eabasics_le_antisymm h2 h1
  exact ⟨cin Y, cmap f, by rw [hsq]; exact hq⟩

/-- **206II at `CvNᵒᵖ`**: the orthocomplement of a sharp predicate is sharp.
Sharpness is an existential over objects *of the subcategory*, so it does
not restrict for free: `cvnsu_isSharp_cpred` pushes `s` forward,
`su_orth_sharp` complements it in `vN_cpsuᵒᵖ`, and the standard corner of
`su_exists_corner` — commutative, hence an object of `CvNᵒᵖ` — brings the
witness back, being an image of `sᗮ` by **203XII** `img_of_compr`. -/
theorem cvnsu_orth_sharp {X : CWStarCPSU.{u}ᵒᵖ}
    {s : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)} (hs : IsSharp s) :
    IsSharp (EffectAlgebra.orth s) := by
  let t : cin X ⟶ effObj (WStarCPSU.{u}ᵒᵖ) := EffectAlgebra.orth (cpred s)
  have h1 : IsSharp t := su_orth_sharp (cvnsu_isSharp_cpred hs)
  obtain ⟨W, π, hπ, -, -, hW⟩ := su_exists_corner t
  have him : IsImage π t := by
    refine ⟨hπ.1, ?_⟩
    intro r hr
    have hkey : imPred (comprMap t) = t := (img_of_compr t).2 t h1
    obtain ⟨α, hα, -⟩ := hπ.2 (comprMap t) (isComprehension_comprMap t).1
    have h2 : comprMap t ≫ r = comprMap t ≫ truth (cin X) := by
      rw [← hα, Category.assoc, hr, ← Category.assoc]
    have h3 := (isImage_imPred (comprMap t)).2 r h2
    rwa [hkey] at h3
  refine ⟨Opposite.op ⟨W.unop, hW (cvn_mul_comm X.unop)⟩, cmk π,
    cpred_injective him.1, ?_⟩
  intro r hr
  exact (cpred_le_iff _ _).mpr (him.2 (cpred r) (congrArg cpred hr))

/-- **206III at `CvNᵒᵖ`** (eff.tex:4460, Examples): the full subcategory
`CvNᵒᵖ` of `vNᵒᵖ` on the commutative von Neumann algebras is a
⋄-effectus. -/
theorem su_diamondEffectus_cvn : DiamondEffectus (CWStarCPSU.{u}ᵒᵖ) :=
  { cvnsuHasQuotients, cvnsuHasComprehension, cvnsuHasImages with
    orth_sharp := fun hs => cvnsu_orth_sharp hs }

/-- The partial-form effectus structure of `CvNᵒᵖ`, bundled. -/
noncomputable def cvnPartialStructure :
    EffectusPartialStructure (CWStarCPSU.{u}ᵒᵖ) :=
  { hasFiniteCoproducts := cvnsuHasFiniteCoproducts
    homPCM := cvnsuPCM
    finPAC := cvnsuFinPAC
    effectus := cvnsuEffectusPartialForm }

section CvNNoDilations

set_option linter.unusedSectionVars false

attribute [local instance] su_diamondEffectus su_diamondEffectus_cvn

/-! ### 221IIIa: `CvNᵒᵖ` has no dilations

**221IIIa** (`exc-cvn-no-dilations`, eff.tex:6812, Exercise; printed
solution bsols.tex:3337–3355).  The print runs in three steps:

1. the standard corner `h_a : 𝒜 → ⌈a⌉𝒜⌈a⌉`, `b ↦ ⌈a⌉b⌈a⌉`, of a
   *commutative* `𝒜` is multiplicative, because
   `⌈a⌉bc⌈a⌉ = ⌈a⌉b⌈a⌉·⌈a⌉c⌈a⌉` by commutativity and idempotence
   (`cvn_corner_mul` and `cvnsu_mul_of_isComprehension` below);
2. every corner is a standard corner up to an isomorphism, so *every*
   corner between commutative von Neumann algebras is nmiu
   (`compr_basics_2`, used inside `cvnsu_mul_of_isComprehension`);
3. if `CvNᵒᵖ` had dilations, every ncpu-map would be a corner after an
   nmiu-map, hence multiplicative — absurd, the average map is not
   (`cvnsu_no_dilations`).

Step 3 has a **gap** in the print, which `total_pure_iso_compr` below
supplies; see the doc comment there. -/

/-- **221IIIa**, step 1 of the print (bsols.tex:3341), as pure algebra: in a
*commutative* ring the standard corner `b ↦ e·b·e` at an idempotent `e` is
multiplicative, `e(xy)e = (exe)(eye)`.  This is the print's computation
`⌈a⌉bc⌈a⌉ = ⌈a⌉b⌈a⌉·⌈a⌉c⌈a⌉`. -/
theorem cvn_corner_mul {A : Type*} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {e : A} (he : e * e = e) (x y : A) :
    e * (x * y) * e = (e * x * e) * (e * y * e) := by
  have hpx : ∀ z : A, e * z * e = e * z := by
    intro z
    rw [mul_assoc, hcomm z e, ← mul_assoc, he]
  rw [hpx, hpx, hpx]
  have e1 : (e * x) * (e * y) = e * ((x * e) * y) := by noncomm_ring
  rw [e1, hcomm x e]
  have e2 : e * ((e * x) * y) = (e * e) * (x * y) := by noncomm_ring
  rw [e2, he]

/-- **221IIIa**, sharpness transports *into* `CvNᵒᵖ`: a sharp predicate `t`
of the ambient `vN_cpsuᵒᵖ` on `cin X` is `cpred s` for a sharp predicate
`s` of `CvNᵒᵖ` on `X`.

This is the second half of `cvnsu_orth_sharp` (VNExamples.lean:8899), read
for an arbitrary sharp `t` instead of `sᗮ`: sharpness is an existential
over objects *of the subcategory*, so it does not restrict for free.  The
standard corner of `su_exists_corner t` is commutative, hence an object of
`CvNᵒᵖ`, and is an image of `t` by **203XII** `img_of_compr` (`im π_t = t`
for sharp `t`); the image transports back along the hom-bijection. -/
theorem cvnsu_isSharp_of_cpred {X : CWStarCPSU.{u}ᵒᵖ}
    {t : cin X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)} (ht : IsSharp t) :
    ∃ s : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ), IsSharp s ∧ cpred s = t := by
  obtain ⟨W, π, hπ, -, -, hW⟩ := su_exists_corner t
  have him : IsImage π t := by
    refine ⟨hπ.1, ?_⟩
    intro r hr
    have hkey : imPred (comprMap t) = t := (img_of_compr t).2 t ht
    obtain ⟨α, hα, -⟩ := hπ.2 (comprMap t) (isComprehension_comprMap t).1
    have h2 : comprMap t ≫ r = comprMap t ≫ truth (cin X) := by
      rw [← hα, Category.assoc, hr, ← Category.assoc]
    have h3 := (isImage_imPred (comprMap t)).2 r h2
    rwa [hkey] at h3
  refine ⟨cmk (X := X) (Y := effObj (CWStarCPSU.{u}ᵒᵖ)) t, ?_, rfl⟩
  refine ⟨Opposite.op ⟨W.unop, hW (cvn_mul_comm X.unop)⟩, cmk π,
    cpred_injective him.1, ?_⟩
  intro r hr
  exact (cpred_le_iff _ _).mpr (him.2 (cpred r) (congrArg cpred hr))

/-- **221IIIa**: a sharp map of `CvNᵒᵖ` (**210I** `SharpMap`,
`Theses/B/Eff/DiamondAmp.lean:1102`) is a sharp map of the ambient
`vN_cpsuᵒᵖ`.  Again this does not hold for free — `SharpMap (cmap f)`
quantifies over *more* predicates than `SharpMap f` — but by
`cvnsu_isSharp_of_cpred` every ambient sharp predicate comes from a sharp
predicate of the subcategory, and `cvnsu_isSharp_cpred`
(VNExamples.lean:7756) pushes the result forward again. -/
theorem cvnsu_sharpMap_cmap {X Y : CWStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hf : SharpMap f) : SharpMap (cmap f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := cvnsu_isSharp_of_cpred ht
  exact cvnsu_isSharp_cpred (hf s hs)

/-- **221IIIa**: totality transports along the hom-bijection, because the
truth predicate of `CvNᵒᵖ` *is* the truth predicate of `vN_cpsuᵒᵖ`
(`cvnsuEffectusPartialForm` sets `one X = cmk (suOne (cin X))`). -/
theorem cvnsu_isTotal_cmap {X Y : CWStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (h : IsTotal f) : IsTotal (cmap f) :=
  congrArg cmap h

/-- The converse of `cvnsu_isTotal_cmap`, by injectivity of `cmap`. -/
theorem cvnsu_isTotal_of_cmap {X Y : CWStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (h : IsTotal (cmap f)) : IsTotal f :=
  cmap_injective h

/-- **221IIIa**: a **sharp total** map of `CvNᵒᵖ` has multiplicative
ncpsu-map.  By `cvnsu_sharpMap_cmap` and `cvnsu_isTotal_cmap` the map is
sharp and total in the ambient `vN_cpsuᵒᵖ`, where **210III**
`su_exists_nmiu_of_sharp_total` (VNExamples.lean:4152) identifies the sharp
total maps with the **nmiu**-maps. -/
theorem cvnsu_mul_of_sharp_total {X Y : CWStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hs : SharpMap f) (ht : IsTotal f) (a b : Y.unop.obj.base.carrier) :
    (cmap f).unop.toNCPMap (a * b)
      = (cmap f).unop.toNCPMap a * (cmap f).unop.toNCPMap b := by
  obtain ⟨ρ, hρ⟩ := su_exists_nmiu_of_sharp_total (cmap f)
    (cvnsu_sharpMap_cmap hs) (cvnsu_isTotal_cmap ht)
  rw [← hρ (a * b), ← hρ a, ← hρ b]
  exact map_mul ρ.toStarAlgHom a b

/-- **221IIIa**: an **isomorphism** of `CvNᵒᵖ` has multiplicative
ncpsu-map.  Isomorphisms are sharp (**221IV.2** `sharpMap_of_isIso`) and
total (`iso_isTotal`), so this is `cvnsu_mul_of_sharp_total`. -/
theorem cvnsu_mul_of_isIso {X Y : CWStarCPSU.{u}ᵒᵖ} (θ : X ⟶ Y) [IsIso θ]
    (a b : Y.unop.obj.base.carrier) :
    (cmap θ).unop.toNCPMap (a * b)
      = (cmap θ).unop.toNCPMap a * (cmap θ).unop.toNCPMap b :=
  cvnsu_mul_of_sharp_total (sharpMap_of_isIso θ) (iso_isTotal θ) a b

/-- **221IIIa**, steps 1–2 of the print (bsols.tex:3339–3348): a
**comprehension** — i.e. a corner — of `CvNᵒᵖ` has multiplicative
ncpsu-map.

Route.  `Theses.B.Dils.standard_corner_dils` (**169IV**) provides the
standard corner `h : 𝒜 → ⌊p⌋𝒜⌊p⌋`, `b ↦ ⌊p⌋b⌊p⌋`, of the effect named by
`p`; it is *unital* into the corner algebra, hence a comprehension for `p`
in `vN_cpsuᵒᵖ` by `su_isComprehension_of_isCornerFor`, and the corner
algebra is commutative because its multiplication is that of `𝒜`, so this
is a comprehension of `CvNᵒᵖ` as well (the universal property restricts to
the subcategory, exactly as in `cvnsuHasComprehension`,
VNExamples.lean:7738).  It is multiplicative by `cvn_corner_mul` — that is
step 1 of the print.  Step 2 is **199VII.2** `compr_basics_2`: any two
comprehensions for `p` differ by a unique isomorphism `θ`, and `θ` is
multiplicative by `cvnsu_mul_of_isIso`. -/
theorem cvnsu_mul_of_isComprehension {W X : CWStarCPSU.{u}ᵒᵖ}
    {p : X ⟶ effObj (CWStarCPSU.{u}ᵒᵖ)} {π : W ⟶ X}
    (hπ : IsComprehension p π) (a b : X.unop.obj.base.carrier) :
    (cmap π).unop.toNCPMap (a * b)
      = (cmap π).unop.toNCPMap a * (cmap π).unop.toNCPMap b := by
  have hcomm : ∀ x y : X.unop.obj.base.carrier, x * y = y * x :=
    cvn_mul_comm X.unop
  let : Theses.VonNeumannAlgebra (Theses.B.Dils.cornerSet
      X.unop.obj.base.carrier (Theses.A.VN.floor (suPredVal (cpred p)))) :=
    Theses.B.Dils.cornerSet_vonNeumannAlgebra _ _
  obtain ⟨h, hval, hcor⟩ := Theses.B.Dils.standard_corner_dils
    (A := X.unop.obj.base.carrier) (suPredVal (cpred p))
    ⟨suPredVal_nonneg (cpred p), suPredVal_le_one (cpred p)⟩
  have hproj : IsStarProjection (Theses.A.VN.floor (suPredVal (cpred p))) :=
    Theses.B.Dils.cornerSet.proj (Theses.A.VN.floor (suPredVal (cpred p)))
  -- the standard corner is unital into `⌊p⌋𝒜⌊p⌋`, whose unit is `⌊p⌋`
  have hunital : h (1 : X.unop.obj.base.carrier) = 1 := by
    refine Theses.B.Dils.cornerSet.val_injective ?_
    rw [hval, Theses.B.Dils.cornerSet.val_one, mul_one]
    exact hproj.isIdempotentElem.eq
  -- the standard corner, as a morphism of `vN_cpsuᵒᵖ`; a `let`, so that its
  -- ncpsu-map is *definitionally* `h`
  let π₁ : Opposite.op (WStarCPSU.of (WStar.of
      (Theses.B.Dils.cornerSet X.unop.obj.base.carrier
        (Theses.A.VN.floor (suPredVal (cpred p)))))) ⟶ cin X :=
    Quiver.Hom.op ⟨h, le_of_eq hunital⟩
  have hπ₁ : π₁.unop.toNCPMap = h := rfl
  -- the corner of a commutative algebra is commutative
  have hWcomm : ∀ x y : Theses.B.Dils.cornerSet X.unop.obj.base.carrier
      (Theses.A.VN.floor (suPredVal (cpred p))), x * y = y * x := by
    intro x y
    refine Theses.B.Dils.cornerSet.val_injective ?_
    rw [Theses.B.Dils.cornerSet.val_mul, Theses.B.Dils.cornerSet.val_mul]
    exact hcomm x.1 y.1
  have hcompr₁ : IsComprehension (cpred p) π₁ :=
    su_isComprehension_of_isCornerFor (cpred p) π₁
      (by rw [hπ₁]; exact hunital) (by rw [hπ₁]; exact hcor)
  let W₁ : CWStarCPSU.{u}ᵒᵖ := Opposite.op ⟨WStarCPSU.of (WStar.of
    (Theses.B.Dils.cornerSet X.unop.obj.base.carrier
      (Theses.A.VN.floor (suPredVal (cpred p))))), hWcomm⟩
  have hcompr₂ : IsComprehension p (cmk (X := W₁) (Y := X) π₁) := by
    refine ⟨cpred_injective hcompr₁.1, ?_⟩
    intro Z g hg
    obtain ⟨g', hg', huniq⟩ := hcompr₁.2 (cmap g) (congrArg cpred hg)
    exact ⟨cmk g', cmap_injective hg',
      fun k hk => cmap_injective (huniq (cmap k) (congrArg cmap hk))⟩
  obtain ⟨θ, hθiso, hθ, -⟩ := compr_basics_2 hπ hcompr₂
  have := hθiso
  have hcmapπ : cmap π = cmap θ ≫ π₁ := congrArg cmap hθ.symm
  have hcomp : ∀ x : X.unop.obj.base.carrier,
      (cmap π).unop.toNCPMap x = (cmap θ).unop.toNCPMap (h x) := fun x => by
    rw [hcmapπ]
    exact suop_comp_apply (cmap θ) π₁ x
  -- step 1 of the print: the standard corner of a *commutative* algebra is
  -- multiplicative
  have hmulh : ∀ x y : X.unop.obj.base.carrier, h (x * y) = h x * h y := by
    intro x y
    refine Theses.B.Dils.cornerSet.val_injective ?_
    rw [Theses.B.Dils.cornerSet.val_mul, hval, hval, hval]
    exact cvn_corner_mul hcomm hproj.isIdempotentElem.eq x y
  have key : (cmap θ).unop.toNCPMap (h (a * b))
      = (cmap θ).unop.toNCPMap (h a) * (cmap θ).unop.toNCPMap (h b) :=
    Eq.trans (congrArg (fun z => (cmap θ).unop.toNCPMap z) (hmulh a b))
      (cvnsu_mul_of_isIso θ (h a) (h b))
  rw [hcomp a, hcomp b, hcomp (a * b)]
  exact key

/-- **221IIIa**: a **total pure** map of `CvNᵒᵖ` has multiplicative
ncpsu-map.  This is the print's "any ncpu-map would be the composition of a
corner and an nmiu-map, and such corners are nmiu", with the missing step
supplied by `total_pure_iso_compr`: a total pure map is an isomorphism
after a comprehension, and both are multiplicative by
`cvnsu_mul_of_isIso` and `cvnsu_mul_of_isComprehension`. -/
theorem cvnsu_mul_of_total_pure {X Y : CWStarCPSU.{u}ᵒᵖ} {f : X ⟶ Y}
    (hp : IsPure f) (ht : IsTotal f) (a b : Y.unop.obj.base.carrier) :
    (cmap f).unop.toNCPMap (a * b)
      = (cmap f).unop.toNCPMap a * (cmap f).unop.toNCPMap b := by
  obtain ⟨Q, θ, π, q, hiso, hπ, rfl⟩ := total_pure_iso_compr hp ht
  have := hiso
  have hcomp : ∀ x : Y.unop.obj.base.carrier,
      (cmap (θ ≫ π)).unop.toNCPMap x
        = (cmap θ).unop.toNCPMap ((cmap π).unop.toNCPMap x) := fun x =>
    suop_comp_apply (cmap θ) (cmap π) x
  simp only [hcomp]
  rw [cvnsu_mul_of_isComprehension hπ]
  exact cvnsu_mul_of_isIso θ _ _

/-- **221IIIa** (`exc-cvn-no-dilations`, eff.tex:6812, Exercise; solution
bsols.tex:3337): **`CvNᵒᵖ` does not have dilations** (**221II**
`HasDilations`).

The print: if `CvNᵒᵖ` had dilations, then every ncpu-map `f = ϱ ∘ h` would
be a corner `h` after an nmiu-map `ϱ`; corners of commutative von Neumann
algebras are multiplicative (steps 1–2, `cvnsu_mul_of_isComprehension`),
hence so would `f` be — absurd.  The witness taken here is the **average**
map `avgNCP : ℂᵤ × ℂᵤ → ℂᵤ` (98X, VNExamples.lean:933), a *unital* ncp-map
which is not multiplicative: it sends `x = (1,0)` and `y = (0,1)` to `½`
each while `x·y = 0`.

The step the print leaves out is the identification of the pure leg `h`
with a corner, supplied by `total_pure_iso_compr`; `h` is total here
because `f = h ≫ ϱ` is and `ϱ` is. -/
theorem cvnsu_no_dilations : ¬ HasDilations (CWStarCPSU.{u}ᵒᵖ) := by
  intro hdil
  -- the average map as a morphism `ℂᵤ ⟶ ℂᵤ × ℂᵤ` of `CvNᵒᵖ`
  obtain ⟨f, hf⟩ : ∃ f : cvnsuI.{u} ⟶ cvnsuP cvnsuI.{u} cvnsuI.{u},
      (cmap f).unop.toNCPMap = avgNCP.{u} :=
    ⟨cmk (Quiver.Hom.op ⟨avgNCP.{u}, le_of_eq avgNCP_unital⟩), rfl⟩
  have hftot : IsTotal f :=
    cvnsu_isTotal_of_cmap ((su_isTotal_iff (cmap f)).mpr (by
      rw [hf]; exact avgNCP_unital))
  obtain ⟨P, ϱ, hleg, hsϱ, htϱ, hpure, hfac, -⟩ := hdil.dil f
  have hhtot : IsTotal hleg := by
    have h1 : hleg ≫ ϱ ≫ truth (cvnsuP cvnsuI.{u} cvnsuI.{u}) = truth cvnsuI.{u} := by
      rw [← Category.assoc, hfac]
      exact hftot
    rwa [show ϱ ≫ truth (cvnsuP cvnsuI.{u} cvnsuI.{u}) = truth P from htϱ] at h1
  -- both legs are multiplicative, hence so is the average map
  have hmulf : ∀ a b : (cvnsuP cvnsuI.{u} cvnsuI.{u}).unop.obj.base.carrier,
      (cmap f).unop.toNCPMap (a * b)
        = (cmap f).unop.toNCPMap a * (cmap f).unop.toNCPMap b := by
    intro a b
    have e1 : ∀ z : (cvnsuP cvnsuI.{u} cvnsuI.{u}).unop.obj.base.carrier,
        (cmap f).unop.toNCPMap z
          = (cmap hleg).unop.toNCPMap ((cmap ϱ).unop.toNCPMap z) := by
      intro z
      conv_lhs => rw [← hfac]
      exact suop_comp_apply (cmap hleg) (cmap ϱ) z
    simp only [e1]
    rw [cvnsu_mul_of_sharp_total hsϱ htϱ,
      cvnsu_mul_of_total_pure hpure hhtot]
  have hmulavg : ∀ x y : ULift.{u} ℂ × ULift.{u} ℂ,
      avgNCP.{u} (x * y) = avgNCP.{u} x * avgNCP.{u} y := by
    intro x y
    have h := hmulf x y
    rw [hf] at h
    exact h
  -- but `avgNCP` is not multiplicative
  have hz : ((ULift.up (1 : ℂ), (0 : ULift.{u} ℂ)) : ULift.{u} ℂ × ULift.{u} ℂ)
      * ((0 : ULift.{u} ℂ), ULift.up (1 : ℂ)) = 0 := by
    refine Prod.ext ?_ ?_
    · show ULift.up (1 : ℂ) * (0 : ULift.{u} ℂ) = 0
      rw [mul_zero]
    · show (0 : ULift.{u} ℂ) * ULift.up (1 : ℂ) = 0
      rw [zero_mul]
  have hL : avgNCP.{u} (0 : ULift.{u} ℂ × ULift.{u} ℂ) = 0 := by
    rw [avgNCP_apply]
    apply ULift.ext
    show (2⁻¹ : ℂ) * ((0 : ℂ) + 0) = 0
    norm_num
  have hR1 : avgNCP.{u} ((ULift.up (1 : ℂ), (0 : ULift.{u} ℂ)))
      = ULift.up (2⁻¹ : ℂ) := by
    rw [avgNCP_apply]
    apply ULift.ext
    show (2⁻¹ : ℂ) * ((1 : ℂ) + 0) = 2⁻¹
    norm_num
  have hR2 : avgNCP.{u} (((0 : ULift.{u} ℂ), ULift.up (1 : ℂ)))
      = ULift.up (2⁻¹ : ℂ) := by
    rw [avgNCP_apply]
    apply ULift.ext
    show (2⁻¹ : ℂ) * ((0 : ℂ) + 1) = 2⁻¹
    norm_num
  have hcon := hmulavg (ULift.up (1 : ℂ), (0 : ULift.{u} ℂ))
    ((0 : ULift.{u} ℂ), ULift.up (1 : ℂ))
  rw [hz, hL, hR1, hR2] at hcon
  have hd : (0 : ℂ) = 2⁻¹ * 2⁻¹ := congrArg ULift.down hcon
  norm_num at hd


end CvNNoDilations

end CvNPartial

/-- **180V at `CvNᵒᵖ`** (`effectus-vn`, eff.tex:827) and **189aI**, second
sentence (`effexamplesintro`, eff.tex:2020): the full subcategory `CvNᵒᵖ` of
the commutative von Neumann algebras is an effectus **in partial form** as
well.  (`effectus_cvn` is the total-form statement; this is the form a
⋄-effectus is built on, and what `diamond_effectus_cvn` uses.)

Neither point gives a proof.  Ours restricts `vnPartialStructure` along the
inclusion `CvNᵒᵖ ⥤ vNᵒᵖ`, which is a bijection on hom-sets: `ℂᵤ`, the
trivial algebra and a product of commutative algebras are commutative, so
the effect object, the initial object and the binary coproducts stay inside
the subcategory, and the hom-PCM, the finPAC axioms and the effect algebra
of 180VII are pulled back.  See the section header above. -/
theorem effectus_cvn_partial :
    Nonempty (EffectusPartialStructure (CWStarCPSU.{u}ᵒᵖ)) :=
  ⟨cvnPartialStructure⟩



section Wrapper

open Theses.A.CStar

/-- **Uniqueness of the effect object of `vN_cpsuᵒᵖ`**, in the form the
hypothetical von Neumann examples need. -/
theorem vn_effObj_iso (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    ∃ θ : s.effectus.I ≅ suI.{u},
      ∀ X : WStarCPSU.{u}ᵒᵖ, s.effectus.one X ≫ θ.hom = suOne X := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact @su_effObj_iso E


end Wrapper


/-! ## `vNᵒᵖ` is real, with separating states and predicates (parsec 190)

The A-dependent statements of `StatesPredicates.lean`. -/

/-- **190III** (eff.tex:2136, Examples): the effectus `vNᵒᵖ` (in partial
form: `(W*_ncpsu)ᵒᵖ`, cf. `effectus_vn_partial`) is a real effectus with
separating states and predicates.  (Its predicates on `𝒜` correspond to the
effects `[0,1]_𝒜` and its states to the normal states.)

`IsRealEffectus` carries the strengthening **190II.3** asks for: the
scalars are not merely in bijective-morphic correspondence with `[0,1]` but
**isomorphic** to it as effect monoids.  See `su_real_separating`. -/
theorem effectus_vn_real_separating
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    IsRealEffectus WStarCPSU.{u}ᵒᵖ ∧
      SeparatingPredicates WStarCPSU.{u}ᵒᵖ ∧
      SeparatingStates WStarCPSU.{u}ᵒᵖ := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact @su_real_separating E

/-! ## `vNᵒᵖ` is a ⋄-effectus and an &-effectus (parsecs 206, 211)

The A-dependent statements of `DiamondAmp.lean`. -/

/-- **206III** (eff.tex:4460, Examples): `vNᵒᵖ` is a ⋄-effectus.  The
`CvNᵒᵖ` clause of the same Examples is `diamond_effectus_cvn` below;
`EJAᵒᵖ` and `Set` are not formalized here. -/
theorem diamond_effectus_vn (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    DiamondEffectus WStarCPSU.{u}ᵒᵖ := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact @su_diamondEffectus E

/-- **206III** (eff.tex:4460, Examples), the `CvNᵒᵖ` clause: the full
subcategory `CvNᵒᵖ` of `vNᵒᵖ` on the **commutative** von Neumann algebras
is a ⋄-effectus too.

The point gives no proof.  Ours restricts the partial-form effectus of
`vNᵒᵖ` along the inclusion `CvNᵒᵖ ⥤ vNᵒᵖ`, which is a bijection on
hom-sets; the only von Neumann fact used is that a corner `p𝒜p` of a
commutative `𝒜` is commutative, which is what makes the quotients (standard
filters) and comprehensions (standard corners) of `vNᵒᵖ` stay inside the
subcategory.  See the section header of `CvNPartial` for the full argument
and `su_diamondEffectus_cvn` for the proof.

Unlike `diamond_effectus_vn` this is stated at the *concrete* partial-form
structure `cvnPartialStructure` rather than at an arbitrary one: the
uniqueness result `vn_effObj_iso` that lets `diamond_effectus_vn` quantify
over all structures has no `CvNᵒᵖ` counterpart in the tree. -/
theorem diamond_effectus_cvn :
    letI := cvnsuHasFiniteCoproducts
    letI := cvnsuPCM
    letI := cvnsuFinPAC
    letI := cvnsuEffectusPartialForm
    DiamondEffectus CWStarCPSU.{u}ᵒᵖ :=
  su_diamondEffectus_cvn

/-! ## The ⋄-self-adjoint square root can be taken pure (**QUESTIONS B15**)

The hypothesis `H` of `su_andThenEffectus_of_pure_sqrt` — that a
⋄-self-adjoint `g` whose square is pure has a *pure* ⋄-self-adjoint square
root with the same square — is discharged below with the witness `h := g`,
by the Theorem of `docs/B15-S.md`:

> an ncp-endomap `g` of a von Neumann algebra with `⌈g⌉ = ⌈g(1)⌉` whose
> square `g ∘ g` is pure is itself pure.

Its carrier hypothesis is **103III**.1 *without* that Exercise's purity
clause — only `g^⋄ = g_⋄` is used in its proof — which
eff-⋄-self-adjointness supplies through
`su_contraposed_of_diamondSelfAdjoint`.  The proof is that document's two
steps, run inside the corner `e𝒜e` for `e = ⌈g⌉` through the bracket
`γ = [g]` of **98IX** `square_f` (an ncpu, faithful endomap of the corner
there, with `g = c_p ∘ γ ∘ π_e` and `p = g(1)`):

* **Step A** (`b15_stepA`): for a projection `s` of the corner, 2-positivity
  of `γ` gives `γ(s)² ≤ γ(s)` (Kadison–Schwarz, `b15_ks`), and 2-positivity
  of `g` at the pair `(√p, γ(s)√p)` gives the Schur inequality `b15_schur`,
  whose regularised form at the spectral projections of `q = g(g(1))`
  increases to `g(g(s)) ≤ g(Ψ)` with `Ψ = √p γ(s)² √p` (`b15_schur_limit`).
  Against `g(g(s)) = g(Ψ) + g(√p (γ(s) − γ(s)²) √p)` and faithfulness of `g`
  on the corner this forces `γ(s) = γ(s)²`; **99II** `gardner` then makes
  `γ` nmiu.
* **Step B** (`b15_stepB`): `γ` nmiu gives `g ∘ g = ad_a ∘ γ²` with
  `a = √γ(p)·√p`, whose two carriers `⌈a*a⌉ = ⌈q⌉` and `⌈aa*⌉ = ⌈γ(p)⌉` are
  both `e`; so the polar phase `[a]` is a *unitary* of the corner and
  `γ² = [a](·)[a]* ∘ [g∘g]`.  Purity of `g ∘ g` makes `[g∘g]` an
  isomorphism (**100III**), hence so is `γ²`, hence so is `γ`, and `g` is
  pure by **100III** again.

Everything in this section is `private` and about an arbitrary von Neumann
algebra; none of it is a point of either thesis.  Two groups of it belong
upstream and should move there once they can be seen from here: the vector
form of 2-positivity and its Schur complement (`b15_twoPos`, `b15_schur`)
into `A/CStar/Matrices.lean` next to **34II** `n_pos`, and the `ε ↓ 0`
monotone limit `⋁ₙ 1_{(1/(n+1),∞)}(q) = ⌈q⌉` with its conjugated form
(`b15_isLUB_spectralProj`, `b15_conj_ceil_limit`) into
`A/Proc/Measurement.lean` next to the spectral projections they are about. -/

section B15SquareRoot

open scoped ComplexOrder CStarAlgebra
open Theses.A.VN Theses.A.Proc

noncomputable section

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Theses.VonNeumannAlgebra A]
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Theses.VonNeumannAlgebra B]

/-- Corners of equal projections are canonically isomorphic (as ncp-maps). -/
private theorem b15_exists_cornerTransport (e e' : A) [Fact (IsStarProjection e)]
    [Fact (IsStarProjection e')] (h : e = e') :
    ∃ τ : NCPMap (Corner A e) (Corner A e'), ∀ x : Corner A e, (τ x).val = x.val := by
  refine ⟨ncpComp (cornerProjMap e').toNCPMap (cornerIncl e).toNCPMap, fun x => ?_⟩
  rw [ncpComp_apply, cornerProjMap_apply, cornerIncl_apply, ← h]
  exact x.property

/-- A positive element below the carrier that is killed by the map is zero. -/
private theorem b15_eq_zero_of_ncpCarrier (f : NCPMap A B) {x : A} (hx : 0 ≤ x)
    (hxe : ceil x ≤ ncpCarrier f) (h : (f x : B) = 0) : x = 0 := by
  have hFF : ∀ a : A, (PositiveLinearMap.ofClass f.toCompletelyPositiveMap a : B) = f a :=
    fun _ => rfl
  have hceil := ncp_ceil (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
    f.preservesDirSups' x hx
  simp only [hFF] at hceil
  rw [h, ceil_zero] at hceil
  have hfs : (f (ceil x) : B) = 0 :=
    (ceil_basic_3 _ (ncpMap_nonneg f (isStarProjection_ceil x).nonneg)).mpr hceil.symm
  have hcspec : IsStarProjection (ncpCarrier f) ∧ (f (1 - ncpCarrier f) : B) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → ncpCarrier f ≤ q :=
    (exists_ncpCarrier f).choose_spec.1
  have hsp := isStarProjection_ceil x
  have hle : ncpCarrier f ≤ 1 - ceil x := by
    refine hcspec.2.2 (1 - ceil x) hsp.one_sub ?_
    have h4 : (1 : A) - (1 - ceil x) = ceil x := by abel
    rw [h4]; exact hfs
  have hc0 : ceil x = 0 := by
    have hconj := star_left_conjugate_le_conjugate (hxe.trans hle) (ceil x)
    rw [hsp.isSelfAdjoint.star_eq] at hconj
    have hL : ceil x * ceil x * ceil x = ceil x := by
      rw [hsp.isIdempotentElem.eq, hsp.isIdempotentElem.eq]
    have hR : ceil x * (1 - ceil x) * ceil x = 0 := by
      have h5 : ceil x * (1 - ceil x) * ceil x
          = ceil x * ceil x - ceil x * ceil x * ceil x := by noncomm_ring
      rw [h5, hL, hsp.isIdempotentElem.eq, sub_self]
    rw [hL, hR] at hconj
    exact le_antisymm hconj hsp.nonneg
  exact (ceil_basic_3 x hx).mpr hc0

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
/-- The vector form of 2-positivity of an ncp-map (**34II**.2 at `N = 2`). -/
private theorem b15_twoPos (f : NCPMap A B) (a : Fin 2 → A) (b : Fin 2 → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j := by
  have h1 : ∀ M : CStarMatrix (Fin 2) (Fin 2) A, 0 ≤ M →
      0 ≤ M.map ⇑(f.toCompletelyPositiveMap.toLinearMap) :=
    fun M hM => f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' 2 M hM
  have h2 := ((Theses.A.CStar.n_pos (f.toCompletelyPositiveMap.toLinearMap) 2).out 0 1).mp h1
  exact h2 a b

/-- The spectral projections `1_{(1/(n+1),∞)}(q)` increase to `⌈q⌉`. -/
private theorem b15_isLUB_spectralProj (q : A) (hq : 0 ≤ q) :
    IsLUB (Set.range fun n : ℕ => spectralProj q ((n : ℝ) + 1)⁻¹) (ceil q) := by
  have hmono : ∀ m n : ℕ, m ≤ n →
      spectralProj q ((m : ℝ) + 1)⁻¹ ≤ spectralProj q ((n : ℝ) + 1)⁻¹ := by
    intro m n hmn
    refine spectralProj_mono hq ?_
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    exact inv_anti₀ hm hle
  set D : Set A := Set.range fun n : ℕ => spectralProj q ((n : ℝ) + 1)⁻¹ with hDdef
  have hproj : ∀ x ∈ D, IsStarProjection x := by
    rintro _ ⟨n, rfl⟩; exact spectralProj_isStarProjection _ _
  have hne : D.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨_, ⟨max m n, rfl⟩, hmono m _ (le_max_left m n), hmono n _ (le_max_right m n)⟩
  have hlub := isLUB_projSup_of_directed D hproj hne hdir
  have heq : projSup D = ceil q := by
    refine projSup_eq hproj (ceil_spec hq).1 ?_ ?_
    · rintro _ ⟨n, rfl⟩
      refine Theses.A.VN.ceil_mono (specPos_nonneg q _) ?_
      have ht : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      rw [specPos]
      conv_rhs => rw [show (q : A) = cfc (fun r : ℝ => r) q from
        (by rw [show (fun r : ℝ => r) = (id : ℝ → ℝ) from rfl]; exact (cfc_id ℝ q).symm)]
      refine cfc_mono fun r hr => ?_
      have h0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg hq hr
      exact max_le (by linarith) h0
    · intro r hr hub
      have hz : ∀ n : ℕ, ((1 : A) - r) * spectralProj q ((n : ℝ) + 1)⁻¹ = 0 := by
        intro n
        have hPn := spectralProj_isStarProjection q ((n : ℝ) + 1)⁻¹
        have h1 : spectralProj q ((n : ℝ) + 1)⁻¹ * r = spectralProj q ((n : ℝ) + 1)⁻¹ :=
          (hPn.le_iff_mul_eq_left hr).mp (hub _ ⟨n, rfl⟩)
        have h2 : r * spectralProj q ((n : ℝ) + 1)⁻¹ = spectralProj q ((n : ℝ) + 1)⁻¹ := by
          have h3 := congrArg star h1
          rwa [star_mul, hPn.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq] at h3
        rw [sub_mul, one_mul, h2, sub_self]
      have hq0 := mul_eq_zero_of_mul_spectralProj_eq_zero hq hz
      have h3 : r * q = q := by
        rw [sub_mul, one_mul, sub_eq_zero] at hq0
        exact hq0.symm
      have hrq : q * r = q := by
        have h4 := congrArg star h3
        rw [star_mul, hr.isSelfAdjoint.star_eq,
          (IsSelfAdjoint.of_nonneg hq).star_eq] at h4
        exact h4
      exact (ceil_le_iff hq hr).mpr hrq
  rwa [heq] at hlub

/-- The `ε ↓ 0` limit: if `c* E c ≤ C` for every spectral projection
`E = 1_{(1/(n+1),∞)}(q)` of a positive `q`, then `c* ⌈q⌉ c ≤ C`. -/
private theorem b15_conj_ceil_limit {q c C : A} (hq : 0 ≤ q)
    (h : ∀ n : ℕ, star c * spectralProj q ((n : ℝ) + 1)⁻¹ * c ≤ C) :
    star c * ceil q * c ≤ C := by
  have hsa : ∀ n : ℕ, IsSelfAdjoint (spectralProj q ((n : ℝ) + 1)⁻¹) :=
    fun n => (spectralProj_isStarProjection _ _).isSelfAdjoint
  have hcsa : IsSelfAdjoint (ceil q) := (isStarProjection_ceil q).isSelfAdjoint
  set D : Set (selfAdjoint A) :=
    Set.range (fun n : ℕ => (⟨spectralProj q ((n : ℝ) + 1)⁻¹, hsa n⟩ : selfAdjoint A))
    with hDdef
  have hval : Subtype.val '' D = Set.range fun n : ℕ => spectralProj q ((n : ℝ) + 1)⁻¹ := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨⟨_, hsa n⟩, ⟨n, rfl⟩, rfl⟩
  have hlubA : IsLUB (Set.range fun n : ℕ => spectralProj q ((n : ℝ) + 1)⁻¹) (ceil q) :=
    b15_isLUB_spectralProj q hq
  have hlubD : IsLUB D (⟨ceil q, hcsa⟩ : selfAdjoint A) := by
    refine isLUB_of_isLUB_val ?_
    rw [hval]
    exact hlubA
  have hne : D.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    have hmono : ∀ i j : ℕ, i ≤ j →
        spectralProj q ((i : ℝ) + 1)⁻¹ ≤ spectralProj q ((j : ℝ) + 1)⁻¹ := by
      intro i j hij
      refine spectralProj_mono hq ?_
      have hm : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hle : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
        have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
        linarith
      exact inv_anti₀ hm hle
    exact ⟨_, ⟨max m n, rfl⟩, hmono m _ (le_max_left m n), hmono n _ (le_max_right m n)⟩
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨_, hlubD.1⟩⟩
  have hds : dirSup D h3 = (⟨ceil q, hcsa⟩ : selfAdjoint A) :=
    (isLUB_dirSup D h3).unique hlubD
  have hAD := ad_normal c D h3
  rw [hds] at hAD
  refine hAD.2 ?_
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact h n

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
/-- The Schur complement inequality carried by 2-positivity. -/
private theorem b15_schur (f : NCPMap A B) (a0 a1 : A) (x : B) :
    star x * f (star a0 * a1) + f (star a1 * a0) * x - star x * f (star a0 * a0) * x
      ≤ f (star a1 * a1) := by
  have h := b15_twoPos f ![a0, a1] ![-x, 1]
  have hsum : ∑ i, ∑ j, star (![-x, 1] i) * f (star (![a0, a1] i) * ![a0, a1] j) * ![-x, 1] j
      = f (star a1 * a1) - (star x * f (star a0 * a1) + f (star a1 * a0) * x
          - star x * f (star a0 * a0) * x) := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_neg, star_one]
    noncomm_ring
  rw [hsum] at h
  exact sub_nonneg.mp h

omit [VonNeumannAlgebra A] [VonNeumannAlgebra B] in
/-- Kadison--Schwarz at a projection for a *unital* ncp-map: `f(s)² ≤ f(s)`. -/
private theorem b15_ks (f : NCPMap A B) (hu : (f 1 : B) = 1) (s : A) (hs : IsStarProjection s) :
    (f s : B) * f s ≤ f s := by
  have hfs : star (f s : B) = f s := by rw [← ncp_star f s, hs.isSelfAdjoint.star_eq]
  have h := b15_schur f 1 s (f s)
  simp only [star_one, one_mul, mul_one, hs.isSelfAdjoint.star_eq,
    hs.isIdempotentElem.eq, hu, hfs] at h
  exact le_trans (le_of_eq (by noncomm_ring)) h

/-- The bracket `[f]` of **98IX** `square_f`, transported to an endomap of the
corner `e𝒜e` for a map whose carrier and the carrier of whose unit value are
both `e`: an ncp-map `e𝒜e → e𝒜e` with the factorisation `f = c_{f(1)} ∘ [f]`,
its unitality, and the fact (**100III** `pure_fundamental`) that `f` is pure
exactly when it is an isomorphism. -/
private theorem b15_exists_bracketEndo (f : NCPMap A A) (e : A) [Fact (IsStarProjection e)]
    (h1 : ncpCarrier f = e) (h2 : ceil (f 1) = e) :
    ∃ b : NCPMap (Corner A e) (Corner A e),
      (∀ x : Corner A e, (f x.val : A)
          = CFC.sqrt (f 1) * (b x).val * CFC.sqrt (f 1)) ∧
        b 1 = 1 ∧
        (Theses.A.Proc.IsPure f ↔ ∃ b' : NCPMap (Corner A e) (Corner A e),
          (∀ x, b' (b x) = x) ∧ ∀ y, b (b' y) = y) := by
  obtain ⟨itr, hitr⟩ := b15_exists_cornerTransport e (ncpCarrier f) h1.symm
  obtain ⟨itr', hitr'⟩ := b15_exists_cornerTransport (ncpCarrier f) e h1
  obtain ⟨ktr, hktr⟩ := b15_exists_cornerTransport (ceil (f 1)) e h2
  obtain ⟨ktr', hktr'⟩ := b15_exists_cornerTransport e (ceil (f 1)) h2.symm
  have hii' : ∀ x : Corner A (ncpCarrier f), itr (itr' x) = x :=
    fun x => Corner.val_injective (by rw [hitr, hitr'])
  have hi'i : ∀ x : Corner A e, itr' (itr x) = x :=
    fun x => Corner.val_injective (by rw [hitr', hitr])
  have hkk' : ∀ y : Corner A e, ktr (ktr' y) = y :=
    fun y => Corner.val_injective (by rw [hktr, hktr'])
  obtain ⟨b, hb⟩ : ∃ b : NCPMap (Corner A e) (Corner A e),
      ∀ x : Corner A e, (b x).val = (sqBracket f (itr x)).val :=
    ⟨ncpComp ktr (ncpComp (sqBracket f) itr), fun x => by
      rw [ncpComp_apply, ncpComp_apply, hktr]⟩
  refine ⟨b, ?_, ?_, ?_⟩
  · intro x
    have hprojx : (cornerProjMap (ncpCarrier f)).toNCPMap x.val = itr x :=
      Corner.val_injective (by rw [cornerProjMap_apply, hitr, h1]; exact x.property)
    have h := (square_f f).1 x.val
    rw [hprojx, stdFilter_apply] at h
    rw [h, hb]
  · refine Corner.val_injective ?_
    have hi1 : itr (1 : Corner A e) = 1 :=
      Corner.val_injective (by rw [hitr]; simp only [Corner.val_one]; exact h1.symm)
    rw [hb, hi1, (square_f f).2.2.1]
    simp only [Corner.val_one]
    exact h2
  · constructor
    · intro hpure
      obtain ⟨-, hinv, hinv1, hinv2⟩ := ((pure_fundamental f).out 0 2).mp hpure
      refine ⟨ncpComp itr' (ncpComp hinv ktr'), fun x => ?_, fun y => ?_⟩
      · rw [ncpComp_apply, ncpComp_apply]
        have hx : ktr' (b x) = sqBracket f (itr x) :=
          Corner.val_injective (by rw [hktr', hb])
        rw [hx, hinv1, hi'i]
      · rw [ncpComp_apply, ncpComp_apply]
        refine Corner.val_injective ?_
        rw [hb, hii', hinv2, hktr']
    · rintro ⟨b', hb'1, hb'2⟩
      have hcond : sqBracket f 1 = 1 ∧
          ∃ h : NCPMap (Corner A (ceil (f 1))) (Corner A (ncpCarrier f)),
            (∀ x, h (sqBracket f x) = x) ∧ ∀ y, sqBracket f (h y) = y := by
        refine ⟨(square_f f).2.2.1, ncpComp itr (ncpComp b' ktr), fun x => ?_, fun y => ?_⟩
        · rw [ncpComp_apply, ncpComp_apply]
          have hbx : ktr (sqBracket f x) = b (itr' x) :=
            Corner.val_injective (by rw [hktr, hb, hii'])
          rw [hbx, hb'1, hii']
        · rw [ncpComp_apply, ncpComp_apply]
          refine Corner.val_injective ?_
          rw [← hb, hb'2, hktr]
      exact ((pure_fundamental f).out 2 0).mp hcond

/-- The regularised Schur bound, taken to the limit.  If the Schur inequality
`x*F + Fx − x*qx ≤ Ψ` holds for every `x`, and `F = √q T √q` for a projection
`T`, then `√q T ⌈q⌉ T √q ≤ Ψ`. -/
private theorem b15_schur_limit {q Psi T : A} (hq0 : 0 ≤ q) (hT : IsStarProjection T)
    (hS : ∀ x : A, star x * (CFC.sqrt q * T * CFC.sqrt q)
      + (CFC.sqrt q * T * CFC.sqrt q) * x - star x * q * x ≤ Psi) :
    CFC.sqrt q * T * ceil q * T * CFC.sqrt q ≤ Psi := by
  set sq : A := CFC.sqrt q with hsqdef
  have hsq0 : (0 : A) ≤ sq := CFC.sqrt_nonneg q
  have hsqs : star sq = sq := (IsSelfAdjoint.of_nonneg hsq0).star_eq
  have hsqsq : sq * sq = q := CFC.sqrt_mul_sqrt_self q hq0
  have hqsq : q * sq = sq * q := by
    calc q * sq = sq * sq * sq := by rw [hsqsq]
      _ = sq * (sq * sq) := by noncomm_ring
      _ = sq * q := by rw [hsqsq]
  have hTs : star T = T := hT.isSelfAdjoint.star_eq
  have hstarc : star (T * sq) = sq * T := by rw [star_mul, hsqs, hTs]
  have hstep : ∀ n : ℕ,
      star (T * sq) * spectralProj q ((n : ℝ) + 1)⁻¹ * (T * sq) ≤ Psi := by
    intro n
    have hd : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    set d : ℝ := ((n : ℝ) + 1)⁻¹ with hddef
    set si : A := specInv q d with hsidef
    set E : A := spectralProj q d with hEdef
    have hEproj : IsStarProjection E := spectralProj_isStarProjection q d
    have hsi0 : (0 : A) ≤ si := specInv_nonneg q hd
    have hsisq : si * sq = sq * si := (specInv_comm q d sq hqsq).symm
    have hsiq : si * q = q * si := (specInv_comm q d q rfl).symm
    have hsis : star si = si := (IsSelfAdjoint.of_nonneg hsi0).star_eq
    have hcont : Continuous (fun r : ℝ => (max r d)⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun r => ne_of_gt (lt_of_lt_of_le hd (le_max_right r d))
    -- `m = 1/max(q,d) · q` is a positive contraction which is `1` on `E`
    have hm0 : (0 : A) ≤ si * q := by
      rw [hsiq]; exact Theses.A.CStar.sqrt_1 q si hq0 hsi0 hsiq.symm
    have hmsa : IsSelfAdjoint (si * q) := IsSelfAdjoint.of_nonneg hm0
    have h1 : si * q = cfc (fun r : ℝ => (max r d)⁻¹ * r) q := by
      rw [cfc_mul (fun r : ℝ => (max r d)⁻¹) (fun r : ℝ => r) q hcont.continuousOn
        (by fun_prop), hsidef, specInv,
        show (fun r : ℝ => r) = (id : ℝ → ℝ) from rfl, cfc_id ℝ q]
    have hmle : si * q ≤ (1 : A) := by
      refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hm0).mp ?_
      rw [h1]
      refine norm_cfc_le zero_le_one fun r hr => ?_
      have hr0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg hq0 hr
      have hmx : (0 : ℝ) < max r d := lt_of_lt_of_le hd (le_max_right r d)
      have hle : (max r d)⁻¹ * r ≤ (max r d)⁻¹ * max r d :=
        mul_le_mul_of_nonneg_left (le_max_left r d) (le_of_lt (inv_pos.mpr hmx))
      rw [inv_mul_cancel₀ (ne_of_gt hmx)] at hle
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (le_of_lt (inv_pos.mpr hmx)) hr0)]
      exact hle
    have hmm : (si * q) * (si * q) ≤ si * q := by
      have hone : IsSelfAdjoint (1 : A) := star_one A
      have h := Theses.A.CStar.sqrt_2 (si * q) hm0 (si * q) 1 hmsa hone rfl
        (by rw [one_mul, mul_one]) hmle
      rwa [mul_one] at h
    have hmE : (si * q) * E = E := specInv_mul_mul_spectralProj hq0 hd
    have hEm : E * (si * q) = E := by
      have h := congrArg star hmE
      rwa [star_mul, hmsa.star_eq, hEproj.isSelfAdjoint.star_eq] at h
    -- `E ≤ u := 2m − m²`
    have huE : (si * q + si * q - (si * q) * (si * q)) * E = E := by
      have hexp : (si * q + si * q - (si * q) * (si * q)) * E
          = (si * q) * E + (si * q) * E - (si * q) * ((si * q) * E) := by noncomm_ring
      simp only [hexp, hmE]
      noncomm_ring
    have hEu : E * (si * q + si * q - (si * q) * (si * q)) = E := by
      have hexp : E * (si * q + si * q - (si * q) * (si * q))
          = E * (si * q) + E * (si * q) - (E * (si * q)) * (si * q) := by noncomm_ring
      simp only [hexp, hEm]
      noncomm_ring
    have hu0 : (0 : A) ≤ si * q + si * q - (si * q) * (si * q) := by
      have h := add_nonneg hm0 (sub_nonneg.mpr hmm)
      have hrw : si * q + (si * q - (si * q) * (si * q))
          = si * q + si * q - (si * q) * (si * q) := by noncomm_ring
      rwa [hrw] at h
    have hucomm : (si * q + si * q - (si * q) * (si * q)) * (1 - E)
        = (1 - E) * (si * q + si * q - (si * q) * (si * q)) := by
      have hl : (si * q + si * q - (si * q) * (si * q)) * (1 - E)
          = (si * q + si * q - (si * q) * (si * q))
            - (si * q + si * q - (si * q) * (si * q)) * E := by noncomm_ring
      have hr : (1 - E) * (si * q + si * q - (si * q) * (si * q))
          = (si * q + si * q - (si * q) * (si * q))
            - E * (si * q + si * q - (si * q) * (si * q)) := by noncomm_ring
      rw [hl, hr, huE, hEu]
    have hEle : E ≤ si * q + si * q - (si * q) * (si * q) := by
      have hnn : (0 : A) ≤ (si * q + si * q - (si * q) * (si * q)) * (1 - E) :=
        Theses.A.CStar.sqrt_1 _ _ hu0 (sub_nonneg.mpr hEproj.le_one) hucomm
      have hrw : (si * q + si * q - (si * q) * (si * q)) * (1 - E)
          = (si * q + si * q - (si * q) * (si * q)) - E := by
        have hl : (si * q + si * q - (si * q) * (si * q)) * (1 - E)
            = (si * q + si * q - (si * q) * (si * q))
              - (si * q + si * q - (si * q) * (si * q)) * E := by noncomm_ring
        rw [hl, huE]
      rw [hrw] at hnn
      exact sub_nonneg.mp hnn
    -- the Schur inequality at `x = (si·√q)·T·√q`
    have hA : (si * sq) * sq = si * q := by rw [mul_assoc, hsqsq]
    have hB : sq * (si * sq) = si * q := by
      rw [← mul_assoc, ← hsisq, mul_assoc, hsqsq]
    have hC : (si * sq) * q * (si * sq) = (si * q) * (si * q) := by
      calc (si * sq) * q * (si * sq) = (si * sq) * (sq * sq) * (si * sq) := by rw [hsqsq]
        _ = ((si * sq) * sq) * (sq * (si * sq)) := by noncomm_ring
        _ = (si * q) * (si * q) := by rw [hA, hB]
    have hstarx : star ((si * sq) * T * sq) = sq * T * (si * sq) := by
      rw [star_mul, star_mul, hsqs, hTs, star_mul, hsis, hsqs, ← hsisq]
      noncomm_ring
    have hS' := hS ((si * sq) * T * sq)
    have hid : star ((si * sq) * T * sq) * (sq * T * sq)
        + (sq * T * sq) * ((si * sq) * T * sq)
        - star ((si * sq) * T * sq) * q * ((si * sq) * T * sq)
        = star (T * sq) * (si * q + si * q - (si * q) * (si * q)) * (T * sq) := by
      rw [hstarx, hstarc]
      calc (sq * T * (si * sq)) * (sq * T * sq) + (sq * T * sq) * ((si * sq) * T * sq)
            - (sq * T * (si * sq)) * q * ((si * sq) * T * sq)
          = sq * T * ((si * sq) * sq) * T * sq + sq * T * (sq * (si * sq)) * T * sq
            - sq * T * ((si * sq) * q * (si * sq)) * T * sq := by noncomm_ring
        _ = sq * T * (si * q) * T * sq + sq * T * (si * q) * T * sq
            - sq * T * ((si * q) * (si * q)) * T * sq := by rw [hA, hB, hC]
        _ = (sq * T) * (si * q + si * q - (si * q) * (si * q)) * (T * sq) := by
            noncomm_ring
    rw [hid] at hS'
    refine le_trans ?_ hS'
    exact star_left_conjugate_le_conjugate hEle (T * sq)
  have hlim := b15_conj_ceil_limit hq0 hstep
  rw [hstarc] at hlim
  calc sq * T * ceil q * T * sq = sq * T * ceil q * (T * sq) := by noncomm_ring
    _ ≤ Psi := hlim

/-- **Step A** of `B15-S.md`: the bracket `γ = [g]` sends projections to
projections. -/
private theorem b15_stepA (g : NCPMap A A) (e : A) [Fact (IsStarProjection e)]
    (gam th : NCPMap (Corner A e) (Corner A e))
    (hgv : ∀ x : Corner A e, (g x.val : A)
      = CFC.sqrt (g 1) * (gam x).val * CFC.sqrt (g 1))
    (hgamu : gam 1 = 1)
    (hfv : ∀ x : Corner A e, (g (g x.val) : A)
      = CFC.sqrt (g (g 1)) * (th x).val * CFC.sqrt (g (g 1)))
    (hthproj : ∀ x : Corner A e, IsStarProjection x → IsStarProjection (th x))
    (hgfaith : ∀ y : A, 0 ≤ y → ceil y ≤ e → (g y : A) = 0 → y = 0)
    (h2 : ceil (g 1) = e) (hf1 : ceil (g (g 1)) = e)
    (s : Corner A e) (hs : IsStarProjection s) : IsStarProjection (gam s) := by
  have heproj : IsStarProjection e := Fact.out
  have hee : e * e = e := heproj.isIdempotentElem.eq
  have hp0 : (0 : A) ≤ g 1 := ncpMap_nonneg g zero_le_one
  have hq0 : (0 : A) ≤ g (g 1) := ncpMap_nonneg g hp0
  have hsp0 : (0 : A) ≤ CFC.sqrt (g 1) := CFC.sqrt_nonneg (g 1)
  have hspstar : star (CFC.sqrt (g 1)) = CFC.sqrt (g 1) :=
    (IsSelfAdjoint.of_nonneg hsp0).star_eq
  have hspsp : CFC.sqrt (g 1) * CFC.sqrt (g 1) = g 1 := CFC.sqrt_mul_sqrt_self (g 1) hp0
  have hGs : star (gam s) = gam s := by rw [← ncp_star gam s, hs.isSelfAdjoint.star_eq]
  have hGstar : star ((gam s).val) = (gam s).val := by
    have h := congrArg Corner.val hGs
    rwa [Corner.val_star] at h
  have hKS : gam s * gam s ≤ gam s := b15_ks gam hgamu s hs
  have hDnn : (0 : A) ≤ (gam s - gam s * gam s).val := sub_nonneg.mpr hKS
  rw [Corner.val_sub, Corner.val_mul] at hDnn
  have hGmem : e * (gam s).val * e = (gam s).val := (gam s).property
  set sp : A := CFC.sqrt (g 1) with hspdef
  set G : A := (gam s).val with hGdef
  -- `√p` lies in the corner
  have hcsp : ceil sp = e := by
    have h := ceil_basic_5 sp hsp0
    rw [sq, hspsp] at h
    rw [← h, h2]
  have hesp : e * sp = sp := ((ceil_basic_1 sp e hsp0 heproj).out 2 0).mp (le_of_eq hcsp)
  have hspe : sp * e = sp := ((ceil_basic_1 sp e hsp0 heproj).out 2 1).mp (le_of_eq hcsp)
  have heG : e * G = G := by
    calc e * G = e * (e * G * e) := by rw [hGmem]
      _ = (e * e) * G * e := by noncomm_ring
      _ = G := by rw [hee, hGmem]
  have hGe : G * e = G := by
    calc G * e = (e * G * e) * e := by rw [hGmem]
      _ = e * G * (e * e) := by noncomm_ring
      _ = G := by rw [hee, hGmem]
  have hgS : (g s.val : A) = sp * G * sp := hgv s
  have hfS : (g (g s.val) : A)
      = CFC.sqrt (g (g 1)) * (th s).val * CFC.sqrt (g (g 1)) := hfv s
  have hTproj : IsStarProjection ((th s).val) :=
    (Corner.isStarProjection_iff (th s)).mp (hthproj s hs)
  have hTmem : e * (th s).val * e = (th s).val := (th s).property
  have hTe : (th s).val * e = (th s).val := by
    calc (th s).val * e = (e * (th s).val * e) * e := by rw [hTmem]
      _ = e * (th s).val * (e * e) := by noncomm_ring
      _ = (th s).val := by rw [hee, hTmem]
  have heT : e * (th s).val = (th s).val := by
    calc e * (th s).val = e * (e * (th s).val * e) := by rw [hTmem]
      _ = (e * e) * (th s).val * e := by noncomm_ring
      _ = (th s).val := by rw [hee, hTmem]
  -- the Schur inequality for `g` at `(√p, γ(s)√p)`
  have hSchur : ∀ x : A, star x * (g (g s.val)) + (g (g s.val)) * x
      - star x * (g (g 1)) * x ≤ g (sp * (G * G) * sp) := by
    intro x
    have hA0 : star sp * sp = g 1 := by rw [hspstar, hspsp]
    have hA1 : star sp * (G * sp) = g s.val := by rw [hspstar, ← mul_assoc, ← hgS]
    have hA2 : star (G * sp) * sp = g s.val := by
      rw [star_mul, hspstar, hGstar, ← hgS]
    have hA3 : star (G * sp) * (G * sp) = sp * (G * G) * sp := by
      rw [star_mul, hspstar, hGstar]; noncomm_ring
    have h := b15_schur g sp (G * sp) x
    rwa [hA0, hA1, hA2, hA3] at h
  -- the `ε ↓ 0` limit
  have hlim := b15_schur_limit hq0 hTproj (by rw [← hfS]; exact hSchur)
  rw [hf1] at hlim
  have hlim' : (g (g s.val) : A) ≤ g (sp * (G * G) * sp) := by
    refine le_trans (le_of_eq ?_) hlim
    rw [hfS]
    calc CFC.sqrt (g (g 1)) * (th s).val * CFC.sqrt (g (g 1))
        = CFC.sqrt (g (g 1)) * ((th s).val * (th s).val) * CFC.sqrt (g (g 1)) := by
          rw [hTproj.isIdempotentElem.eq]
      _ = CFC.sqrt (g (g 1)) * ((th s).val * e * (th s).val) * CFC.sqrt (g (g 1)) := by
          rw [hTe]
      _ = CFC.sqrt (g (g 1)) * (th s).val * e * (th s).val * CFC.sqrt (g (g 1)) := by
          noncomm_ring
  -- squeeze
  have hsplit : (g s.val : A) = sp * (G * G) * sp + sp * (G - G * G) * sp := by
    rw [hgS]; noncomm_ring
  have hadd : (g (g s.val) : A)
      = g (sp * (G * G) * sp) + g (sp * (G - G * G) * sp) := by
    rw [hsplit]; exact map_add g.toCompletelyPositiveMap _ _
  have hDpos : (0 : A) ≤ sp * (G - G * G) * sp := by
    have h := star_left_conjugate_nonneg hDnn sp
    rwa [hspstar] at h
  have hzeroD : (g (sp * (G - G * G) * sp) : A) = 0 := by
    refine le_antisymm ?_ (ncpMap_nonneg g hDpos)
    rw [hadd] at hlim'
    have h2' : (g (sp * (G * G) * sp) : A) + g (sp * (G - G * G) * sp)
        ≤ g (sp * (G * G) * sp) + 0 := by rw [add_zero]; exact hlim'
    exact le_of_add_le_add_left h2'
  -- faithfulness kills `√p D √p`
  have hmemD : e * (G - G * G) * e = G - G * G := by
    calc e * (G - G * G) * e = e * G * e - (e * G) * (G * e) := by noncomm_ring
      _ = G - G * G := by rw [hGmem, heG, hGe]
  have hDzero : sp * (G - G * G) * sp = 0 := by
    refine hgfaith _ hDpos ?_ hzeroD
    refine (ceil_le_iff hDpos heproj).mpr ?_
    rw [mul_assoc, hspe]
  -- hence `D = 0`
  have hsD0 : (0 : A) ≤ CFC.sqrt (G - G * G) := CFC.sqrt_nonneg _
  have hsDs : star (CFC.sqrt (G - G * G)) = CFC.sqrt (G - G * G) :=
    (IsSelfAdjoint.of_nonneg hsD0).star_eq
  have hsDsD : CFC.sqrt (G - G * G) * CFC.sqrt (G - G * G) = G - G * G :=
    CFC.sqrt_mul_sqrt_self _ hDnn
  have hz : star (CFC.sqrt (G - G * G) * sp) * (CFC.sqrt (G - G * G) * sp) = 0 := by
    rw [star_mul, hspstar, hsDs]
    calc sp * CFC.sqrt (G - G * G) * (CFC.sqrt (G - G * G) * sp)
        = sp * (CFC.sqrt (G - G * G) * CFC.sqrt (G - G * G)) * sp := by noncomm_ring
      _ = sp * (G - G * G) * sp := by rw [hsDsD]
      _ = 0 := hDzero
  have h0 : CFC.sqrt (G - G * G) * sp = 0 :=
    (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have h1 : CFC.sqrt (G - G * G) * (g 1) = 0 := by
    rw [← hspsp, ← mul_assoc, h0, zero_mul]
  have h2'' : CFC.sqrt (G - G * G) * e = 0 := by
    rw [← h2]; exact mul_ceil_eq_zero hp0 h1
  have hsDmem : e * CFC.sqrt (G - G * G) * e = CFC.sqrt (G - G * G) :=
    Corner.sqrt_mem (G - G * G) hDnn hmemD
  have hsDzero : CFC.sqrt (G - G * G) = 0 := by
    rw [← hsDmem, mul_assoc, h2'', mul_zero]
  have hD0 : G - G * G = 0 := by rw [← hsDsD, hsDzero, mul_zero]
  refine (Corner.isStarProjection_iff (gam s)).mpr ⟨?_, hGstar⟩
  show G * G = G
  have := sub_eq_zero.mp hD0
  exact this.symm

/-- **Step B** of `B15-S.md`: once `γ = [g]` is nmiu, `f = ad_a ∘ γ²` with `a`
of full carrier on both sides, so `γ²` — and hence `γ` — is an isomorphism. -/
private theorem b15_stepB (g : NCPMap A A) (e : A) [Fact (IsStarProjection e)]
    (gam th thi : NCPMap (Corner A e) (Corner A e))
    (hgv : ∀ x : Corner A e, (g x.val : A)
      = CFC.sqrt (g 1) * (gam x).val * CFC.sqrt (g 1))
    (hgamu : gam 1 = 1)
    (hgammul : ∀ x y : Corner A e, gam (x * y) = gam x * gam y)
    (hgamceil : ∀ x : Corner A e, 0 ≤ x → ceil (gam x) = gam (ceil x))
    (hfv : ∀ x : Corner A e, (g (g x.val) : A)
      = CFC.sqrt (g (g 1)) * (th x).val * CFC.sqrt (g (g 1)))
    (hthi1 : ∀ x, thi (th x) = x) (hthi2 : ∀ y, th (thi y) = y)
    (h2 : ceil (g 1) = e) (hf1 : ceil (g (g 1)) = e) :
    ∃ δ : NCPMap (Corner A e) (Corner A e),
      (∀ x, δ (gam x) = x) ∧ ∀ y, gam (δ y) = y := by
  have heproj : IsStarProjection e := Fact.out
  have hee : e * e = e := heproj.isIdempotentElem.eq
  have hes : star e = e := heproj.isSelfAdjoint.star_eq
  have hp0 : (0 : A) ≤ g 1 := ncpMap_nonneg g zero_le_one
  have hq0 : (0 : A) ≤ g (g 1) := ncpMap_nonneg g hp0
  have hsp0 : (0 : A) ≤ CFC.sqrt (g 1) := CFC.sqrt_nonneg (g 1)
  have hspstar : star (CFC.sqrt (g 1)) = CFC.sqrt (g 1) :=
    (IsSelfAdjoint.of_nonneg hsp0).star_eq
  have hspsp : CFC.sqrt (g 1) * CFC.sqrt (g 1) = g 1 := CFC.sqrt_mul_sqrt_self (g 1) hp0
  have hep : e * (g 1) = g 1 := ((ceil_basic_1 (g 1) e hp0 heproj).out 2 0).mp (le_of_eq h2)
  have hpe : (g 1) * e = g 1 := ((ceil_basic_1 (g 1) e hp0 heproj).out 2 1).mp (le_of_eq h2)
  have hPmem : e * (g 1) * e = g 1 := by rw [hep, hpe]
  -- `p` as an element of the corner, and `ρ = γ(p)`
  set P : Corner A e := ⟨g 1, hPmem⟩ with hPdef
  have hPval : P.val = g 1 := rfl
  have hP0 : (0 : Corner A e) ≤ P := hp0
  have hsqrtP : (CFC.sqrt P).val = CFC.sqrt (g 1) := by
    rw [Corner.val_sqrt P hP0, hPval]
  have hR0 : (0 : Corner A e) ≤ gam P := ncpMap_nonneg gam hP0
  have hgamsqrtP : gam (CFC.sqrt P) = CFC.sqrt (gam P) := by
    refine (CFC.sqrt_unique ?_ (ncpMap_nonneg gam (CFC.sqrt_nonneg P))).symm
    rw [← hgammul, CFC.sqrt_mul_sqrt_self P hP0]
  have hrhoval : (gam (CFC.sqrt P)).val = CFC.sqrt ((gam P).val) := by
    rw [hgamsqrtP, Corner.val_sqrt (gam P) hR0]
  have hrho0 : (0 : A) ≤ (gam P).val := hR0
  have hceilP : ceil P = 1 := by
    refine Corner.val_injective ?_
    rw [Corner.val_ceil P hP0, hPval, Corner.val_one, h2]
  have hceilrho : ceil ((gam P).val) = e := by
    have h := hgamceil P hP0
    rw [hceilP, hgamu] at h
    have h' := congrArg Corner.val h
    rwa [Corner.val_ceil (gam P) hR0, Corner.val_one] at h'
  -- `a = √ρ √p`
  set a : A := CFC.sqrt ((gam P).val) * CFC.sqrt (g 1) with hadef
  have hsr0 : (0 : A) ≤ CFC.sqrt ((gam P).val) := CFC.sqrt_nonneg _
  have hsrstar : star (CFC.sqrt ((gam P).val)) = CFC.sqrt ((gam P).val) :=
    (IsSelfAdjoint.of_nonneg hsr0).star_eq
  have hsrsr : CFC.sqrt ((gam P).val) * CFC.sqrt ((gam P).val) = (gam P).val :=
    CFC.sqrt_mul_sqrt_self _ hrho0
  have hastar : star a = CFC.sqrt (g 1) * CFC.sqrt ((gam P).val) := by
    rw [hadef, star_mul, hspstar, hsrstar]
  have haa : star a * a = g (g 1) := by
    rw [hastar, hadef]
    calc CFC.sqrt (g 1) * CFC.sqrt ((gam P).val)
          * (CFC.sqrt ((gam P).val) * CFC.sqrt (g 1))
        = CFC.sqrt (g 1)
            * (CFC.sqrt ((gam P).val) * CFC.sqrt ((gam P).val)) * CFC.sqrt (g 1) := by
          noncomm_ring
      _ = CFC.sqrt (g 1) * (gam P).val * CFC.sqrt (g 1) := by rw [hsrsr]
      _ = g (g 1) := by rw [← hgv P, hPval]
  have hsupp : suppProj a = e := by rw [suppProj, haa, hf1]
  have hcsr : ceil (CFC.sqrt ((gam P).val)) = e := by
    have h := ceil_basic_5 (CFC.sqrt ((gam P).val)) hsr0
    rw [sq, hsrsr] at h
    rw [← h, hceilrho]
  have hsre : CFC.sqrt ((gam P).val) * e = CFC.sqrt ((gam P).val) :=
    ((ceil_basic_1 _ e hsr0 heproj).out 2 1).mp (le_of_eq hcsr)
  have hrange : rangeProj a = e := by
    have hrw : a * star a
        = star (CFC.sqrt ((gam P).val)) * (g 1) * CFC.sqrt ((gam P).val) := by
      rw [hastar, hadef, hsrstar]
      calc CFC.sqrt ((gam P).val) * CFC.sqrt (g 1)
            * (CFC.sqrt (g 1) * CFC.sqrt ((gam P).val))
          = CFC.sqrt ((gam P).val) * (CFC.sqrt (g 1) * CFC.sqrt (g 1))
              * CFC.sqrt ((gam P).val) := by noncomm_ring
        _ = _ := by rw [hspsp]
    rw [rangeProj, hrw, ceil_fundamental_1 _ (g 1) hp0, h2, hsrstar, hsre, hsrsr,
      hceilrho]
  -- the polar phase `u = [a]` is a unitary of the corner
  obtain ⟨-, hpol1, hpol2⟩ := polar_decomposition a
  obtain ⟨-, hpolss, hpolrr⟩ := polar_decomposition_1 a
  set u : A := polar a with hudef
  rw [hsupp] at hpolss hpol2
  rw [hrange] at hpolrr
  rw [haa] at hpol1
  have hue : u * e = u := hpol2
  have heu : e * u = u := by
    calc e * u = (u * star u) * u := by rw [hpolrr]
      _ = u * (star u * u) := by noncomm_ring
      _ = u * e := by rw [hpolss]
      _ = u := hue
  have hesu : e * star u = star u := by
    have h := congrArg star hue
    rwa [star_mul, hes] at h
  have hsue : star u * e = star u := by
    have h := congrArg star heu
    rwa [star_mul, hes] at h
  -- `f = ad_a ∘ γ²`
  have hsq0 : (0 : A) ≤ CFC.sqrt (g (g 1)) := CFC.sqrt_nonneg _
  have hsqstar : star (CFC.sqrt (g (g 1))) = CFC.sqrt (g (g 1)) :=
    (IsSelfAdjoint.of_nonneg hsq0).star_eq
  have hfa : ∀ x : Corner A e, (g (g x.val) : A) = star a * (gam (gam x)).val * a := by
    intro x
    have hmem : (CFC.sqrt P * gam x * CFC.sqrt P).val
        = CFC.sqrt (g 1) * (gam x).val * CFC.sqrt (g 1) := by
      rw [Corner.val_mul, Corner.val_mul, hsqrtP]
    have h1 : (g x.val : A) = (CFC.sqrt P * gam x * CFC.sqrt P).val := by
      rw [hmem, hgv x]
    rw [h1, hgv (CFC.sqrt P * gam x * CFC.sqrt P), hgammul, hgammul, Corner.val_mul,
      Corner.val_mul, hrhoval, hastar, hadef]
    noncomm_ring
  -- `ϑ = ad_{[a]} ∘ γ²`
  have hthval : ∀ x : Corner A e,
      (th x).val = star u * (gam (gam x)).val * u := by
    intro x
    refine ad_injective (CFC.sqrt (g (g 1))) e
      (hf1.symm.trans (ceil_eq_rangeProj_sqrt hq0)) (th x).property ?_ ?_
    · have hc1 : e * (star u * (gam (gam x)).val * u) * e
          = (e * star u) * (gam (gam x)).val * (u * e) := by noncomm_ring
      rw [hc1, hesu, hue]
    · rw [hsqstar]
      have hl : CFC.sqrt (g (g 1)) * (th x).val * CFC.sqrt (g (g 1)) = g (g x.val) :=
        (hfv x).symm
      rw [hl, hfa x, hpol1, star_mul, hsqstar]
      noncomm_ring
  -- the conjugations by `[a]` and its adjoint
  have hble : star (star u) * e * star u ≤ e := by
    rw [star_star]
    exact le_of_eq (by rw [hue, hpolrr])
  have hbrle : star u * e * u ≤ e := le_of_eq (by rw [hsue, hpolss])
  obtain ⟨bta, hbta0⟩ := exists_adNCP (star u) e e hble
  obtain ⟨btb, hbtb⟩ := exists_adNCP u e e hbrle
  have hbta : ∀ z : Corner A e, (bta z).val = u * z.val * star u := by
    intro z
    rw [hbta0, star_star]
  have hbab : ∀ z : Corner A e, bta (btb z) = z := by
    intro z
    refine Corner.val_injective ?_
    rw [hbta, hbtb]
    calc u * (star u * z.val * u) * star u
        = (u * star u) * z.val * (u * star u) := by noncomm_ring
      _ = z.val := by rw [hpolrr]; exact z.property
  have hbba : ∀ z : Corner A e, btb (bta z) = z := by
    intro z
    refine Corner.val_injective ?_
    rw [hbtb, hbta]
    calc star u * (u * z.val * star u) * u
        = (star u * u) * z.val * (star u * u) := by noncomm_ring
      _ = z.val := by rw [hpolss]; exact z.property
  -- `γ² = β ∘ ϑ`
  have hgam2 : ∀ x : Corner A e, gam (gam x) = bta (th x) := by
    intro x
    refine Corner.val_injective ?_
    rw [hbta, hthval x]
    calc (gam (gam x)).val
        = e * (gam (gam x)).val * e := (gam (gam x)).property.symm
      _ = (u * star u) * (gam (gam x)).val * (u * star u) := by rw [hpolrr]
      _ = u * (star u * (gam (gam x)).val * u) * star u := by noncomm_ring
  -- the inverse
  obtain ⟨k, hk⟩ : ∃ k : NCPMap (Corner A e) (Corner A e),
      ∀ z, k z = thi (btb z) := ⟨ncpComp thi btb, fun z => ncpComp_apply _ _ _⟩
  have hk1 : ∀ z, gam (gam (k z)) = z := by
    intro z
    rw [hgam2, hk, hthi2, hbab]
  have hk2 : ∀ x, k (gam (gam x)) = x := by
    intro x
    rw [hgam2, hk, hbba, hthi1]
  have hinj : Function.Injective ⇑gam := by
    intro x y hxy
    have h : gam (gam x) = gam (gam y) := by rw [hxy]
    have h2 := congrArg k h
    rwa [hk2, hk2] at h2
  refine ⟨ncpComp gam k, fun x => ?_, fun y => ?_⟩
  · rw [ncpComp_apply]
    refine hinj ?_
    exact hk1 (gam x)
  · rw [ncpComp_apply]
    exact hk1 y

/-- **B15-S.md**, the Theorem: an ncp-endomap `g` of a von Neumann algebra
with `⌈g⌉ = ⌈g(1)⌉` whose square `g ∘ g` is pure is itself pure. -/
private theorem b15_pure_of_pure_sq_aux (g : NCPMap A A) (e : A) [Fact (IsStarProjection e)]
    (h1 : ncpCarrier g = e) (h2 : ceil (g 1) = e)
    (hfpure : Theses.A.Proc.IsPure (ncpComp g g)) : Theses.A.Proc.IsPure g := by
  have heproj : IsStarProjection e := Fact.out
  have hp0 : (0 : A) ≤ g 1 := ncpMap_nonneg g zero_le_one
  have hcspec : IsStarProjection (ncpCarrier g) ∧ (g (1 - ncpCarrier g) : A) = 0 ∧
      ∀ q : A, IsStarProjection q → g (1 - q) = 0 → ncpCarrier g ≤ q :=
    (exists_ncpCarrier g).choose_spec.1
  have hcz : (g (1 - e) : A) = 0 := by rw [← h1]; exact hcspec.2.1
  have hge : (g e : A) = g 1 := by
    have hs : (g (1 - e) : A) = g 1 - g e := map_sub g.toCompletelyPositiveMap 1 e
    rw [hcz] at hs
    exact (sub_eq_zero.mp hs.symm).symm
  have hgfaith : ∀ y : A, 0 ≤ y → ceil y ≤ e → (g y : A) = 0 → y = 0 :=
    fun y hy hye hgy => b15_eq_zero_of_ncpCarrier g hy (by rw [h1]; exact hye) hgy
  have hFF : ∀ a : A, (PositiveLinearMap.ofClass g.toCompletelyPositiveMap a : A) = g a :=
    fun _ => rfl
  have hf1 : ceil (g (g 1)) = e := by
    have h := ncp_ceil (PositiveLinearMap.ofClass g.toCompletelyPositiveMap)
      g.preservesDirSups' (g 1) hp0
    simp only [hFF] at h
    rw [h, h2, hge, h2]
  have hcarf : ncpCarrier (ncpComp g g) = e := by
    have hcspecf : IsStarProjection (ncpCarrier (ncpComp g g)) ∧
        (ncpComp g g (1 - ncpCarrier (ncpComp g g)) : A) = 0 ∧
        ∀ q : A, IsStarProjection q → ncpComp g g (1 - q) = 0 →
          ncpCarrier (ncpComp g g) ≤ q :=
      (exists_ncpCarrier (ncpComp g g)).choose_spec.1
    refine le_antisymm (hcspecf.2.2 e heproj ?_) ?_
    · rw [ncpComp_apply, hcz]
      exact map_zero g.toCompletelyPositiveMap
    · have hz := hcspecf.2.1
      rw [ncpComp_apply] at hz
      have hnn : (0 : A) ≤ 1 - ncpCarrier (ncpComp g g) := sub_nonneg.mpr hcspecf.1.le_one
      have hyc : ceil (g (1 - ncpCarrier (ncpComp g g))) ≤ e := by
        rw [← h2]; exact ceil_le_ceil_one g _ hnn
      have hgz := hgfaith _ (ncpMap_nonneg g hnn) hyc hz
      have hcg := hcspec.2.2 (ncpCarrier (ncpComp g g)) hcspecf.1 hgz
      rwa [h1] at hcg
  have hf1' : ceil (ncpComp g g 1) = e := by rwa [ncpComp_apply]
  obtain ⟨gam, hgv, hgamu, hgiff⟩ := b15_exists_bracketEndo g e h1 h2
  obtain ⟨th, hfv0, hthu, hthiff⟩ := b15_exists_bracketEndo (ncpComp g g) e hcarf hf1'
  obtain ⟨thi, hthi1, hthi2⟩ := hthiff.mp hfpure
  have hfv : ∀ x : Corner A e, (g (g x.val) : A)
      = CFC.sqrt (g (g 1)) * (th x).val * CFC.sqrt (g (g 1)) := by
    intro x
    have h := hfv0 x
    rwa [ncpComp_apply, ncpComp_apply] at h
  -- `[f]` is an nmiu-isomorphism (**99IX**)
  have hthi1u : thi 1 = 1 := by
    have h := hthi1 1
    rwa [hthu] at h
  have hthiso := Theses.A.Proc.iso (⟨th, le_of_eq hthu⟩ : NCPSUMap (Corner A e) (Corner A e))
    (⟨thi, le_of_eq hthi1u⟩ : NCPSUMap (Corner A e) (Corner A e)) hthi1 hthi2
  have hthproj : ∀ x : Corner A e, IsStarProjection x → IsStarProjection (th x) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · show th x * th x = th x
      rw [← hthiso.2.1, hx.isIdempotentElem.eq]
    · show star (th x) = th x
      rw [← hthiso.2.2 x, hx.isSelfAdjoint.star_eq]
  -- Step A, then Gardner (**99II**)
  have hgamproj : ∀ x : Corner A e, IsStarProjection x → IsStarProjection (gam x) :=
    fun x hx => b15_stepA g e gam th hgv hgamu hfv hthproj hgfaith h2 hf1 x hx
  have hgammul : ∀ x y : Corner A e, gam (x * y) = gam x * gam y :=
    ((gardner gam hgamu).out 3 0).mp hgamproj
  have hgamceil : ∀ x : Corner A e, 0 ≤ x → ceil (gam x) = gam (ceil x) :=
    ((gardner gam hgamu).out 3 4).mp hgamproj
  -- Step B
  obtain ⟨dl, hdl1, hdl2⟩ :=
    b15_stepB g e gam th thi hgv hgamu hgammul hgamceil hfv hthi1 hthi2 h2 hf1
  exact hgiff.mpr ⟨dl, hdl1, hdl2⟩

/-- **B15-S.md**, the Theorem, at the canonical corner. -/
private theorem b15_pure_of_pure_sq (g : NCPMap A A) (hcar : ncpCarrier g = ceil (g 1))
    (hfpure : Theses.A.Proc.IsPure (ncpComp g g)) : Theses.A.Proc.IsPure g :=
  b15_pure_of_pure_sq_aux g (ceil (g 1)) hcar rfl hfpure

end

end B15SquareRoot

/-- **211IV** (`vn-is-andthen-eff`, eff.tex:4859, Examples): `vNᵒᵖ` is an
&-effectus, with `asrt_a(b) = √a b √a` (as are `CvNᵒᵖ` and `EJAᵒᵖ`, not
formalized here; these are the only known examples).

**Reduced to a single missing step** — see
`su_andThenEffectus_of_pure_sqrt` and the section header above it.  Both
axioms of **211II** are proved for `vNᵒᵖ`:

* axiom 2 (`quot_after_compr_pure`) outright, as
  `su_quot_after_compr_pure`, which is eff.tex:4862's citation of **100III**
  `pure-fundamental`;
* axiom 1 (`existsUnique_asrt`): existence is `su_exists_asrt`, and
  uniqueness is `su_asrt_unique_of_pure_sqrt`, i.e. **105V**
  `positive-map-uniqueness` reached through the two translations
  `su_procPure_of_isPure` (eff-purity ⟹ proc-purity, 100I) and
  `su_contraposed_of_diamondSelfAdjoint` (eff-⋄-self-adjointness ⟹
  proc-contraposition, 101VI).

The hypothesis `H` of `su_andThenEffectus_of_pure_sqrt` is supplied here.
**eff.tex 206II.4 does not require the ⋄-self-adjoint square root `g` of a
⋄-positive map to be pure, where proc.tex 103I does**, so 105V is a
statement about a strictly smaller class of maps than 211II.1 quantifies
over; `H` says the two classes agree in `vNᵒᵖ`, and they do, with the
witness `h := g`: a ⋄-self-adjoint `g` whose square is pure is *itself*
pure.  Neither thesis proves that; it is the Theorem of `docs/B15-S.md`,
formalized in the section above as `b15_pure_of_pure_sq` (recorded as
**QUESTIONS B15**). -/
theorem vn_is_andthen_eff (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    AndThenEffectus WStarCPSU.{u}ᵒᵖ := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  let inst_epf := E
  let inst_diam := @su_diamondEffectus E
  refine @su_andThenEffectus_of_pure_sqrt E (@su_diamondEffectus E) ?_
  -- a ⋄-self-adjoint `g` whose square is pure *is itself pure*
  -- (`docs/B15-S.md`, `b15_pure_of_pure_sq`), so `h := g` will do
  intro X g hgsa hpure
  refine ⟨g, su_isPure_of_procPure (b15_pure_of_pure_sq g.unop.toNCPMap ?_ ?_),
    hgsa, rfl⟩
  · -- `⌈g⌉ = ⌈g(1)⌉`: **103III**.1 without its purity clause
    have hcon := su_contraposed_of_diamondSelfAdjoint hgsa
    have hd : Theses.A.Proc.diamondUp g.unop.toNCPMap 1
        = Theses.A.Proc.diamondDown g.unop.toNCPMap 1 :=
      (Theses.A.Proc.contraposed_iff_diamond _ _).mpr hcon 1
        (IsStarProjection.one (R := X.unop.base.carrier))
    rw [← Theses.A.Proc.diamondDown_one g.unop.toNCPMap, ← hd]
    rfl
  · have h := su_procPure_of_isPure hpure
    have heq : (g ≫ g).unop.toNCPMap
        = Theses.A.Proc.ncpComp g.unop.toNCPMap g.unop.toNCPMap := by
      refine DFunLike.ext _ _ fun y => ?_
      rw [Theses.A.Proc.ncpComp_apply]
      exact suop_comp_apply g g y
    rwa [heq] at h

/-! ## `vNᵒᵖ` is a †-effectus, and has dilations (parsecs 215, 221, 223)

The A-dependent statements of `Dagger.lean`. -/

/-- **215VI** (`vn-is-dagger-category`, eff.tex:5338, Corollary): the
&-effectus `vNᵒᵖ` is a †-effectus. -/
theorem vn_is_dagger_category (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      Nonempty (DaggerEffectus WStarCPSU.{u}ᵒᵖ) := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact fun hA => @su_daggerEffectus E hA

/-- **221III** (eff.tex:6805, Example): the effectus `vNᵒᵖ` has dilations
(Paschke dilations; the full subcategory `CvNᵒᵖ` does not — that is 221IIIa,
`cvnsu_no_dilations`). -/
theorem vn_has_dilations (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hD : DiamondEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hD
      HasDilations WStarCPSU.{u}ᵒᵖ := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact fun hD => @su_hasDilations E hD

/-- **223VI** (eff.tex:7095, Example): every dilation in `vNᵒᵖ` has the
order correspondence (by the Paschke correspondence of the dils
chapter). -/
theorem vn_dilation_order_correspondence
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ∀ {X Y P : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) (ϱ : P ⟶ Y) (h : X ⟶ P),
        IsDilation f ϱ h → DilationOrderCorrespondence f ϱ h := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  intro hA X Y P f ϱ h hd
  exact @su_dilation_order_correspondence E hA X Y P f ϱ h hd

/-! ## `Pure (vNᵒᵖ)`, and the effects of a von Neumann algebra (parsecs 224, 225)

The A-dependent statements of `Comparisons.lean`. -/

/-- **224VI** (`exc-purec-no-biproduct`, eff.tex:7189, Exercise\*):
`Pure (vNᵒᵖ)` does not have finite (bi)products — in particular it has no
binary coproducts. -/
theorem exc_purec_no_biproduct (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasBinaryCoproducts (PureCat WStarCPSU.{u}ᵒᵖ) := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact fun hA => @su_exc_purec_no_biproduct E hA

/-- **224VII** (`exc-purec-equal`, eff.tex:7218, Exercise\*):
`Pure (vNᵒᵖ)` does not have all coequalizers. -/
theorem exc_purec_equal (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasCoequalizers (PureCat WStarCPSU.{u}ᵒᵖ) := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact fun hA => @su_exc_purec_equal E hA

/-! ### The sequential product `a & b = √a b √a` (225V)

eff.tex:7381 asserts 225V without proof, and 225VI — which proves (S1), (S2),
(S3) for a †-effectus — is not a route to the remaining three axioms.  The
mathematics supplied here is the Gudder–Greechie characterisation

> `√a b √a = √b a √b` **iff** `ab = ba`,

`commute_of_sqrtConj_eq` / `sqrtConj_comm_of_commute` below; the three
commutation axioms (S4a), (S4b), (S5) are immediate from it, because once
`a` and `b` commute `a & b` is just `ab`.  Nothing in this block uses the
effectus structure, so 225V never depended on 180V.

The hard direction is `commute_of_sqrtConj_eq`, and the argument is:
with `s = √a`, `t = √b` the hypothesis says exactly that `x = st` is
**normal** (`x x* = s b s`, `x* x = t a t`); writing `x = s₁·(s₁t)` with
`s₁ = √s` and using `quasispectrum (cd) = quasispectrum (dc)` transports the
spectrum of the *positive* element `s₁ t s₁` onto `x`, so `x` is normal with
spectrum in `ℝ≥0`, hence positive, hence self-adjoint: `st = ts`. -/

section SequentialEffects

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Anything commuting with `a` commutes with `√a` (`CFC.sqrt` is a
`cfcₙ` over `ℝ≥0`). -/
theorem commute_sqrt {a b : A} (h : Commute a b) : Commute (CFC.sqrt a) b :=
  h.cfcₙ_nnreal NNReal.sqrt

/-- If `x` is normal and `x = c * d` with `d * c ≥ 0`, then `x ≥ 0`: the
`ℂ`- and `ℝ`-quasispectra of `cd` and `dc` agree, so `x` is normal with real
spectrum (hence self-adjoint) and with nonnegative spectrum (hence
positive). -/
theorem nonneg_of_normal_of_swap {x c d : A} (hx : x = c * d) (hcd : 0 ≤ d * c)
    (hn : Commute (star x) x) : 0 ≤ x := by
  have hqℂ : quasispectrum ℂ (d * c) = quasispectrum ℂ x := by
    rw [hx, quasispectrum.mul_comm]
  have hqℝ : quasispectrum ℝ (d * c) = quasispectrum ℝ x := by
    rw [hx, quasispectrum.mul_comm]
  have hsa : IsSelfAdjoint x := by
    have h1 : QuasispectrumRestricts (d * c) Complex.reCLM :=
      (IsSelfAdjoint.of_nonneg hcd).quasispectrumRestricts
    exact isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr
      ⟨⟨hn⟩, h1.of_quasispectrum_eq hqℂ⟩
  refine nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr ⟨hsa, ?_⟩
  exact (QuasispectrumRestricts.nnreal_of_nonneg hcd).of_quasispectrum_eq hqℝ

/-- The product of two nonnegative elements is nonnegative as soon as it is
normal (`st = √s · (√s t)` and `(√s t) · √s = √s t √s ≥ 0`). -/
theorem nonneg_mul_of_normal {s t : A} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hn : Commute (star (s * t)) (s * t)) : 0 ≤ s * t := by
  have hs1 : (0 : A) ≤ CFC.sqrt s := CFC.sqrt_nonneg s
  have hss : CFC.sqrt s * CFC.sqrt s = s := CFC.sqrt_mul_sqrt_self s hs
  refine nonneg_of_normal_of_swap (c := CFC.sqrt s) (d := CFC.sqrt s * t) ?_ ?_ hn
  · rw [← mul_assoc, hss]
  · exact conjugate_nonneg_of_nonneg ht hs1

/-- The **sequential product** of 225V, `a & b = √a b √a`, on the whole
algebra. -/
noncomputable def sqrtConj (a b : A) : A := CFC.sqrt a * b * CFC.sqrt a

theorem sqrtConj_nonneg {a b : A} (hb : 0 ≤ b) : 0 ≤ sqrtConj a b :=
  conjugate_nonneg_of_nonneg hb (CFC.sqrt_nonneg a)

theorem sqrtConj_le_one {a b : A} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : b ≤ 1) :
    sqrtConj a b ≤ 1 := by
  refine le_trans (conjugate_le_conjugate_of_nonneg hb (CFC.sqrt_nonneg a)) ?_
  rw [show CFC.sqrt a * 1 * CFC.sqrt a = a by
    rw [mul_one, CFC.sqrt_mul_sqrt_self a ha]]
  exact ha1

theorem sqrtConj_one_left (b : A) : sqrtConj 1 b = b := by
  simp [sqrtConj, CFC.sqrt_one]

theorem sqrtConj_add (a b c : A) :
    sqrtConj c a + sqrtConj c b = sqrtConj c (a + b) := by
  simp only [sqrtConj]; noncomm_ring

/-- **Gudder–Greechie**, the content of 225V: for positive `a, b`,
`√a b √a = √b a √b` forces `ab = ba`. -/
theorem commute_of_sqrtConj_eq {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : sqrtConj a b = sqrtConj b a) : Commute a b := by
  simp only [sqrtConj] at h
  set s : A := CFC.sqrt a with hsdef
  set t : A := CFC.sqrt b with htdef
  have hs : (0 : A) ≤ s := CFC.sqrt_nonneg a
  have ht : (0 : A) ≤ t := CFC.sqrt_nonneg b
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha
  have htt : t * t = b := CFC.sqrt_mul_sqrt_self b hb
  have hsst : star s = s := (IsSelfAdjoint.of_nonneg hs).star_eq
  have htst : star t = t := (IsSelfAdjoint.of_nonneg ht).star_eq
  have hstar : star (s * t) = t * s := by rw [star_mul, hsst, htst]
  have hnorm : Commute (star (s * t)) (s * t) := by
    show star (s * t) * (s * t) = (s * t) * star (s * t)
    rw [hstar]
    calc t * s * (s * t) = t * (s * s) * t := by noncomm_ring
      _ = t * a * t := by rw [hss]
      _ = s * b * s := h.symm
      _ = s * (t * t) * s := by rw [htt]
      _ = s * t * (t * s) := by noncomm_ring
  have hpos : (0 : A) ≤ s * t := nonneg_mul_of_normal hs ht hnorm
  have hst : s * t = t * s := by
    have hx := (IsSelfAdjoint.of_nonneg hpos).star_eq
    rw [hstar] at hx
    exact hx.symm
  have hc : Commute s t := hst
  have h1 : Commute s b := by rw [← htt]; exact hc.mul_right hc
  have h2 : Commute a b := by rw [← hss]; exact h1.mul_left h1
  exact h2

theorem sqrtConj_eq_mul_of_commute {a b : A} (ha : 0 ≤ a) (h : Commute a b) :
    sqrtConj a b = a * b := by
  have hc : Commute (CFC.sqrt a) b := commute_sqrt h
  calc sqrtConj a b = CFC.sqrt a * (b * CFC.sqrt a) := by rw [sqrtConj, mul_assoc]
    _ = CFC.sqrt a * (CFC.sqrt a * b) := by rw [hc.eq]
    _ = CFC.sqrt a * CFC.sqrt a * b := by rw [mul_assoc]
    _ = a * b := by rw [CFC.sqrt_mul_sqrt_self a ha]

/-- The converse half of Gudder–Greechie. -/
theorem sqrtConj_comm_of_commute {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Commute a b) : sqrtConj a b = sqrtConj b a := by
  rw [sqrtConj_eq_mul_of_commute ha h, sqrtConj_eq_mul_of_commute hb h.symm, h.eq]

/-- `√(ab) = √a √b` for commuting nonnegative `a, b`. -/
theorem sqrt_mul_of_commute {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Commute a b) :
    CFC.sqrt (a * b) = CFC.sqrt a * CFC.sqrt b := by
  have hc : Commute (CFC.sqrt a) (CFC.sqrt b) :=
    (commute_sqrt (commute_sqrt h).symm).symm
  refine CFC.sqrt_unique ?_ (hc.mul_nonneg (CFC.sqrt_nonneg a) (CFC.sqrt_nonneg b))
  calc CFC.sqrt a * CFC.sqrt b * (CFC.sqrt a * CFC.sqrt b)
      = CFC.sqrt a * (CFC.sqrt b * CFC.sqrt a) * CFC.sqrt b := by noncomm_ring
    _ = CFC.sqrt a * (CFC.sqrt a * CFC.sqrt b) * CFC.sqrt b := by rw [hc.eq]
    _ = CFC.sqrt a * CFC.sqrt a * (CFC.sqrt b * CFC.sqrt b) := by noncomm_ring
    _ = a * b := by rw [CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]

/-- Axiom (S3): `√a b √a = star u * u` and `√b a √b = u * star u` for
`u = √b √a`, so either vanishing forces `u = 0`. -/
theorem sqrtConj_eq_zero_comm {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : sqrtConj a b = 0) : sqrtConj b a = 0 := by
  simp only [sqrtConj] at h ⊢
  set s : A := CFC.sqrt a with hsdef
  set t : A := CFC.sqrt b with htdef
  have hs : (0 : A) ≤ s := CFC.sqrt_nonneg a
  have ht : (0 : A) ≤ t := CFC.sqrt_nonneg b
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha
  have htt : t * t = b := CFC.sqrt_mul_sqrt_self b hb
  have hsst : star s = s := (IsSelfAdjoint.of_nonneg hs).star_eq
  have htst : star t = t := (IsSelfAdjoint.of_nonneg ht).star_eq
  have hstar : star (t * s) = s * t := by rw [star_mul, hsst, htst]
  have hzero : star (t * s) * (t * s) = 0 := by
    rw [hstar]
    calc s * t * (t * s) = s * (t * t) * s := by noncomm_ring
      _ = s * b * s := by rw [htt]
      _ = 0 := h
  have hu : t * s = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hzero
  calc t * a * t = (t * s) * (s * t) := by rw [← hss]; noncomm_ring
    _ = 0 := by rw [hu, zero_mul]

/-- Axiom (S4b): with `ab = ba` one has `√(ab) = √a√b`, so both sides are
`√a √b c √b √a`. -/
theorem sqrtConj_assoc_of_commute {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Commute a b) (c : A) :
    sqrtConj (sqrtConj a b) c = sqrtConj a (sqrtConj b c) := by
  have hc : Commute (CFC.sqrt a) (CFC.sqrt b) :=
    (commute_sqrt (commute_sqrt h).symm).symm
  have hab : sqrtConj a b = a * b := sqrtConj_eq_mul_of_commute ha h
  have hsq : CFC.sqrt (a * b) = CFC.sqrt a * CFC.sqrt b :=
    sqrt_mul_of_commute ha hb h
  rw [show sqrtConj (sqrtConj a b) c = sqrtConj (a * b) c by rw [hab]]
  simp only [sqrtConj, hsq]
  calc CFC.sqrt a * CFC.sqrt b * c * (CFC.sqrt a * CFC.sqrt b)
      = CFC.sqrt a * CFC.sqrt b * c * (CFC.sqrt b * CFC.sqrt a) := by rw [hc.eq]
    _ = CFC.sqrt a * (CFC.sqrt b * c * CFC.sqrt b) * CFC.sqrt a := by noncomm_ring

variable [Theses.VonNeumannAlgebra A]

/-- The sequential product `a & b = √a b √a` on the effects `[0,1]_𝒜`. -/
noncomputable def effSeq (a b : Theses.effects A) : Theses.effects A :=
  ⟨sqrtConj (a : A) (b : A), sqrtConj_nonneg b.2.1,
    sqrtConj_le_one a.2.1 a.2.2 b.2.2⟩

/-- **225V** (eff.tex:7381, Examples), the structure: `[0,1]_𝒜` with
`a & b = √a b √a`. -/
noncomputable def effectsSEA : SequentialEffectAlgebra (Theses.effects A) where
  seq := effSeq
  seq_add := fun c {a b} h => by
    have hab : (a : A) + (b : A) ≤ 1 := h
    have hperp : Perp (effSeq c a) (effSeq c b) := by
      show sqrtConj (c : A) (a : A) + sqrtConj (c : A) (b : A) ≤ 1
      rw [sqrtConj_add]
      exact sqrtConj_le_one c.2.1 c.2.2 hab
    exact ⟨hperp, Subtype.ext (sqrtConj_add _ _ _)⟩
  one_seq := fun a => Subtype.ext (sqrtConj_one_left (a : A))
  seq_zero_comm := fun a b hab =>
    Subtype.ext (sqrtConj_eq_zero_comm a.2.1 b.2.1 (congrArg Subtype.val hab))
  seq_comm_orth := fun {a b} h => by
    have hcomm : Commute (a : A) (b : A) :=
      commute_of_sqrtConj_eq a.2.1 b.2.1 (congrArg Subtype.val h)
    have hb' : (0 : A) ≤ 1 - (b : A) := sub_nonneg.mpr b.2.2
    have hc2 : Commute (a : A) (1 - (b : A)) :=
      (Commute.one_right (a : A)).sub_right hcomm
    exact Subtype.ext (sqrtConj_comm_of_commute a.2.1 hb' hc2)
  seq_comm_assoc := fun {a b} h c => by
    have hcomm : Commute (a : A) (b : A) :=
      commute_of_sqrtConj_eq a.2.1 b.2.1 (congrArg Subtype.val h)
    exact Subtype.ext (sqrtConj_assoc_of_commute a.2.1 b.2.1 hcomm (c : A))
  seq_comm_compat := fun {a b c} h hca hcb => by
    have h1 : Commute (c : A) (a : A) :=
      commute_of_sqrtConj_eq c.2.1 a.2.1 (congrArg Subtype.val hca)
    have h2 : Commute (c : A) (b : A) :=
      commute_of_sqrtConj_eq c.2.1 b.2.1 (congrArg Subtype.val hcb)
    have hsa : Commute (c : A) (CFC.sqrt (a : A)) := (commute_sqrt h1.symm).symm
    have h3 : Commute (c : A) (sqrtConj (a : A) (b : A)) :=
      (hsa.mul_right h2).mul_right hsa
    have h4 : Commute (c : A) ((a : A) + (b : A)) := h1.add_right h2
    exact ⟨Subtype.ext (sqrtConj_comm_of_commute c.2.1 (sqrtConj_nonneg b.2.1) h3),
      Subtype.ext (sqrtConj_comm_of_commute c.2.1 (add_nonneg a.2.1 b.2.1) h4)⟩

end SequentialEffects

/-- **225V** (eff.tex:7381, Examples): the effect algebra `[0,1]_𝒜` of a
von Neumann algebra is a sequential effect algebra with
`a & b = √a b √a`.

The "with `a & b = √a b √a`" is **in the statement**: a bare
`Nonempty (SequentialEffectAlgebra (effects A))` would assert only that
*some* sequential product exists on `[0,1]_𝒜`, and the point names the one
it means.  The structure is `effectsSEA` above. -/
theorem effects_sea (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    ∃ S : SequentialEffectAlgebra (Theses.effects A),
      ∀ a b : Theses.effects A,
        (S.seq a b : A) = CFC.sqrt (a : A) * (b : A) * CFC.sqrt (a : A) :=
  ⟨effectsSEA, fun _ _ => rfl⟩

/-! ## 195V.5: the unit interval of `L^∞[0,1]` is an effect divisoid

195V is an *Examples* point that prints no argument for this clause (its
parenthetical `basic-divisoid-equiv` is 195VI, the criterion for `C(X)`,
which would reach `L^∞` only through a hyperstonean spectrum and Gelfand
duality).  So the proof class here is `none` and what follows is a direct
construction: the effect monoid on `[0,1]_𝒜` for a *commutative* von Neumann
algebra `𝒜`, the order bridge identifying `L^∞(X, μ)` with bounded
measurable functions modulo null sets *as an ordered* algebra, and then the
pointwise division `f/g = min (f/g) 1` off the null set `{g = 0}`.

The other half of the clause — that the unit interval of `C[0,1]` is *not*
an effect divisoid — is `cIcc_unitInterval_not_divisoid` in
`B/Eff/StatesPredicates.lean`.  This half must live here because `L^∞`
exists in the tree only as thesis A's `Linfty μ`, and (author ruling,
2026-08-17) thesis B may import thesis A only through this file. -/

section LinftyDivisoid

open scoped ComplexOrder
open Filter MeasureTheory Theses.A.VN

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-! ### Bounded measurable functions: closure properties

`Theses.A.VN.IsBoundedMeasurable X f` is `Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C`;
thesis A's own closure lemmas for it are `private`, so they are redone here. -/

/-- `𝓛^∞(X)` is closed under `star`. -/
theorem isBoundedMeasurable_star {g : X → ℂ} (hg : IsBoundedMeasurable X g) :
    IsBoundedMeasurable X (star g) := by
  obtain ⟨hm, C, hC⟩ := hg
  have hs : Measurable fun x => star (g x) :=
    Complex.continuous_conj.measurable.comp hm
  exact ⟨hs, C, fun x => by simpa using hC x⟩

/-- `𝓛^∞(X)` is closed under multiplication. -/
theorem isBoundedMeasurable_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f * g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, max Cf 0 * max Cg 0, fun x => ?_⟩
  have h1 : ‖f x‖ ≤ max Cf 0 := (hCf x).trans (le_max_left _ _)
  have h2 : ‖g x‖ ≤ max Cg 0 := (hCg x).trans (le_max_left _ _)
  calc ‖(f * g) x‖ = ‖f x‖ * ‖g x‖ := by simp
    _ ≤ max Cf 0 * max Cg 0 := mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)

/-- `𝓛^∞(X)` is closed under scalars. -/
theorem isBoundedMeasurable_smul (z : ℂ) {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (z • f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.const_smul z, ‖z‖ * max C 0, fun x => ?_⟩
  have hx : ‖(z • f) x‖ = ‖z‖ * ‖f x‖ := by simp
  rw [hx]
  exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg z)

/-- `𝓛^∞(X)` is closed under addition. -/
theorem isBoundedMeasurable_add {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f + g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.add hgm, Cf + Cg, fun x => ?_⟩
  calc ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ Cf + Cg := add_le_add (hCf x) (hCg x)

/-- `𝓛^∞(X)` is closed under subtraction. -/
theorem isBoundedMeasurable_sub {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f - g) := by
  have he : f - g = f + (-1 : ℂ) • g := by funext x; simp [sub_eq_add_neg]
  rw [he]
  exact isBoundedMeasurable_add hf (isBoundedMeasurable_smul _ hg)

/-! ### Bounded measurable *real* functions -/

/-- A bounded measurable *real* function on `X` — the shape in which the
elements of `[0,1]_{L^∞}` will be handled. -/
def IsBoundedMeasurableReal (X : Type u) [MeasurableSpace X] (r : X → ℝ) : Prop :=
  Measurable r ∧ ∃ C, ∀ x, |r x| ≤ C

/-- A bounded measurable real function is a bounded measurable function. -/
theorem IsBoundedMeasurableReal.toComplex {r : X → ℝ}
    (hr : IsBoundedMeasurableReal X r) : IsBoundedMeasurable X fun x => (r x : ℂ) := by
  obtain ⟨hm, C, hC⟩ := hr
  exact ⟨Complex.measurable_ofReal.comp hm, C, fun x => by
    simpa [Real.norm_eq_abs] using hC x⟩

/-- A `[0,1]`-valued measurable function is bounded measurable. -/
theorem isBoundedMeasurableReal_of_Icc {r : X → ℝ} (hm : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (h1 : ∀ x, r x ≤ 1) : IsBoundedMeasurableReal X r :=
  ⟨hm, 1, fun x => abs_le.mpr ⟨by linarith [h0 x], h1 x⟩⟩

/-- Bounded measurable real functions are closed under multiplication. -/
theorem IsBoundedMeasurableReal.mul {f g : X → ℝ} (hf : IsBoundedMeasurableReal X f)
    (hg : IsBoundedMeasurableReal X g) : IsBoundedMeasurableReal X (f * g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, max Cf 0 * max Cg 0, fun x => ?_⟩
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
    (abs_nonneg _) (le_max_right _ _)

/-! ### The order bridge for `L^∞(X, μ)`

Thesis A's `linfty_le_iff` is `private`, so the two directions are proved
here from the public interface alone: `0 ≤ [f]` in `L^∞(X, μ)` iff `f` is
almost everywhere a nonnegative real. -/

/-- The positive cone of `L^∞(X, μ)`, pointwise: `0 ≤ [f]` exactly when `f`
is `μ`-almost everywhere a nonnegative real number.

`(⇐)` is `[f] = star [√f] ⊙ [√f]`; `(⇒)` takes a bounded measurable
representative `g` of `√[f]` (which is self-adjoint), so that
`f =ᵐ star g ⋅ g` pointwise. -/
theorem linfty_mk_nonneg_iff {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    0 ≤ Linfty.mk μ f ↔ ∀ᵐ x ∂μ, (0 : ℂ) ≤ f x := by
  constructor
  · intro h
    obtain ⟨g, hg, hgm⟩ := Linfty.mk_surjective (CFC.sqrt (Linfty.mk μ f))
    have hsa : IsSelfAdjoint (CFC.sqrt (Linfty.mk μ f)) :=
      (CFC.sqrt_nonneg (Linfty.mk μ f)).isSelfAdjoint
    have hsq : CFC.sqrt (Linfty.mk μ f) * CFC.sqrt (Linfty.mk μ f) = Linfty.mk μ f :=
      CFC.sqrt_mul_sqrt_self _ h
    have key : Linfty.mk μ f = Linfty.mk μ (star g * g) := by
      rw [Linfty.mk_mul (isBoundedMeasurable_star hg) hg, Linfty.mk_star hg, hgm,
        hsa.star_eq, hsq]
    have hae := (Linfty.mk_eq_iff hf
      (isBoundedMeasurable_mul (isBoundedMeasurable_star hg) hg)).mp key
    filter_upwards [hae] with x hx
    rw [hx]
    exact star_mul_self_nonneg (g x)
  · intro h
    set r : X → ℝ := fun x => Real.sqrt (f x).re with hrdef
    obtain ⟨hfm, C, hC⟩ := hf
    have hrm : Measurable r :=
      Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hfm)
    have hrr : IsBoundedMeasurableReal X r := by
      refine ⟨hrm, Real.sqrt (max C 0), fun x => ?_⟩
      have h1 : (f x).re ≤ max C 0 :=
        ((le_abs_self _).trans
          ((Complex.abs_re_le_norm (f x)).trans (hC x))).trans (le_max_left _ _)
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt h1
    have hrb : IsBoundedMeasurable X fun x => (r x : ℂ) := hrr.toComplex
    have hstar : star (fun x => (r x : ℂ)) = fun x => (r x : ℂ) := by funext x; simp
    have hys : star (Linfty.mk μ fun x => (r x : ℂ)) = Linfty.mk μ fun x => (r x : ℂ) := by
      rw [← Linfty.mk_star hrb, hstar]
    have hfe : f =ᵐ[μ] (fun x => (r x : ℂ)) * (fun x => (r x : ℂ)) := by
      filter_upwards [h] with x hx
      obtain ⟨h1, h2⟩ := Complex.le_def.mp hx
      simp only [Complex.zero_re, Complex.zero_im] at h1 h2
      show f x = (r x : ℂ) * (r x : ℂ)
      rw [hrdef]
      simp only
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h1]
      exact Complex.ext rfl (by simp [← h2])
    rw [Linfty.mk_congr (⟨hfm, C, hC⟩ : IsBoundedMeasurable X f)
      (isBoundedMeasurable_mul hrb hrb) hfe, Linfty.mk_mul hrb hrb]
    calc (0 : Linfty μ)
        ≤ star (Linfty.mk μ fun x => (r x : ℂ)) * Linfty.mk μ fun x => (r x : ℂ) :=
          star_mul_self_nonneg _
      _ = (Linfty.mk μ fun x => (r x : ℂ)) * Linfty.mk μ fun x => (r x : ℂ) := by rw [hys]

/-- `f ↦ [f]` turns subtraction into subtraction (thesis A exports only
`Linfty.mk_add` and `Linfty.mk_smul`). -/
theorem linfty_mk_sub {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) :
    Linfty.mk μ (f - g) = Linfty.mk μ f - Linfty.mk μ g := by
  have he : f - g = f + (-1 : ℂ) • g := by funext x; simp [sub_eq_add_neg]
  rw [he, Linfty.mk_add hf (isBoundedMeasurable_smul _ hg), Linfty.mk_smul _ hg]
  simp [sub_eq_add_neg]

/-- The order of `L^∞(X, μ)` is the almost-everywhere pointwise order. -/
theorem linfty_mk_le_iff {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) :
    Linfty.mk μ f ≤ Linfty.mk μ g ↔ ∀ᵐ x ∂μ, f x ≤ g x := by
  rw [← sub_nonneg, ← linfty_mk_sub hg hf,
    linfty_mk_nonneg_iff (isBoundedMeasurable_sub hg hf)]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · exact sub_nonneg.mp hx
  · exact sub_nonneg.mpr hx

variable (μ) in
/-- The class in `L^∞(X, μ)` of a real-valued function. -/
noncomputable def linftyMkR (r : X → ℝ) : Linfty μ := Linfty.mk μ fun x => (r x : ℂ)

/-- Two real functions have the same class iff they agree almost everywhere. -/
theorem linftyMkR_eq_iff {f g : X → ℝ} (hf : IsBoundedMeasurableReal X f)
    (hg : IsBoundedMeasurableReal X g) : linftyMkR μ f = linftyMkR μ g ↔ f =ᵐ[μ] g := by
  rw [linftyMkR, linftyMkR, Linfty.mk_eq_iff hf.toComplex hg.toComplex]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · exact Complex.ofReal_injective hx
  · exact congrArg _ hx

/-- The order of `L^∞(X, μ)` on classes of real functions. -/
theorem linftyMkR_le_iff {f g : X → ℝ} (hf : IsBoundedMeasurableReal X f)
    (hg : IsBoundedMeasurableReal X g) :
    linftyMkR μ f ≤ linftyMkR μ g ↔ ∀ᵐ x ∂μ, f x ≤ g x := by
  rw [linftyMkR, linftyMkR, linfty_mk_le_iff hf.toComplex hg.toComplex]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · exact Complex.real_le_real.mp hx
  · exact Complex.real_le_real.mpr hx

/-- The positive cone of `L^∞(X, μ)` on classes of real functions. -/
theorem linftyMkR_nonneg_iff {f : X → ℝ} (hf : IsBoundedMeasurableReal X f) :
    0 ≤ linftyMkR μ f ↔ ∀ᵐ x ∂μ, 0 ≤ f x := by
  rw [linftyMkR, linfty_mk_nonneg_iff hf.toComplex]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · exact Complex.zero_le_real.mp hx
  · exact Complex.zero_le_real.mpr hx

/-- `f ↦ [f]` is multiplicative on real functions. -/
theorem linftyMkR_mul {f g : X → ℝ} (hf : IsBoundedMeasurableReal X f)
    (hg : IsBoundedMeasurableReal X g) :
    linftyMkR μ (f * g) = linftyMkR μ f * linftyMkR μ g := by
  have he : (fun x => (((f * g) x : ℝ) : ℂ))
      = (fun x => (f x : ℂ)) * (fun x => (g x : ℂ)) := by funext x; simp
  rw [linftyMkR, he, Linfty.mk_mul hf.toComplex hg.toComplex]
  rfl

/-- `f ↦ [f]` is unital. -/
theorem linftyMkR_one : linftyMkR μ (1 : X → ℝ) = 1 := by
  have he : (fun x => (((1 : X → ℝ) x : ℝ) : ℂ)) = (1 : X → ℂ) := by funext x; simp
  rw [linftyMkR, he, Linfty.mk_one]

/-- The constant `1` is a bounded measurable real function. -/
theorem isBoundedMeasurableReal_one : IsBoundedMeasurableReal X (1 : X → ℝ) :=
  isBoundedMeasurableReal_of_Icc measurable_const (fun _ => zero_le_one) (fun _ => le_refl 1)

/-- A `[0,1]`-valued measurable function has its class in `[0,1]_{L^∞}`. -/
theorem linftyMkR_mem_effects {r : X → ℝ} (hm : Measurable r) (h0 : ∀ x, 0 ≤ r x)
    (h1 : ∀ x, r x ≤ 1) : linftyMkR μ r ∈ Theses.effects (Linfty μ) := by
  have hb : IsBoundedMeasurableReal X r := isBoundedMeasurableReal_of_Icc hm h0 h1
  refine ⟨(linftyMkR_nonneg_iff hb).mpr (Filter.Eventually.of_forall h0), ?_⟩
  rw [← linftyMkR_one (μ := μ)]
  exact (linftyMkR_le_iff hb isBoundedMeasurableReal_one).mpr
    (Filter.Eventually.of_forall h1)

/-- Every effect of `L^∞(X, μ)` is the class of a `[0,1]`-valued measurable
function: truncate any representative to `x ↦ min (max (f x).re 0) 1`, which
is almost everywhere equal to it by the order bridge. -/
theorem linfty_exists_unit_rep (a : Theses.effects (Linfty μ)) :
    ∃ r : X → ℝ, Measurable r ∧ (∀ x, 0 ≤ r x) ∧ (∀ x, r x ≤ 1) ∧
      linftyMkR μ r = (a : Linfty μ) := by
  obtain ⟨f, hf, hfa⟩ := Linfty.mk_surjective (a : Linfty μ)
  have h0 : ∀ᵐ x ∂μ, (0 : ℂ) ≤ f x := by
    refine (linfty_mk_nonneg_iff hf).mp ?_
    rw [hfa]; exact a.2.1
  have h1 : ∀ᵐ x ∂μ, f x ≤ 1 := by
    have hle : Linfty.mk μ f ≤ Linfty.mk μ (1 : X → ℂ) := by
      rw [hfa, Linfty.mk_one]; exact a.2.2
    exact (linfty_mk_le_iff hf ⟨measurable_const, 1, fun _ => by simp⟩).mp hle
  have hmeas : Measurable fun x => min (max (f x).re 0) 1 :=
    ((Complex.measurable_re.comp hf.1).max measurable_const).min measurable_const
  refine ⟨fun x => min (max (f x).re 0) 1, hmeas,
    fun x => le_min (le_max_right _ _) zero_le_one, fun _ => min_le_right _ _, ?_⟩
  rw [linftyMkR, ← hfa]
  refine Linfty.mk_congr (IsBoundedMeasurableReal.toComplex
    (isBoundedMeasurableReal_of_Icc hmeas
      (fun x => le_min (le_max_right _ _) zero_le_one)
      (fun _ => min_le_right _ _))) hf ?_
  filter_upwards [h0, h1] with x hx0 hx1
  obtain ⟨hr0, hi0⟩ := Complex.le_def.mp hx0
  obtain ⟨hr1, -⟩ := Complex.le_def.mp hx1
  simp only [Complex.zero_re, Complex.zero_im, Complex.one_re] at hr0 hi0 hr1
  show ((min (max (f x).re 0) 1 : ℝ) : ℂ) = f x
  rw [max_eq_left hr0, min_eq_left hr1]
  exact Complex.ext rfl (by simp [← hi0])

/-! ### (a) The effect monoid on the effects of a commutative von Neumann algebra -/

section CommEffects

variable {A : Type u} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For commuting effects `a ⊙ b ≤ 1`: `a ⋅ (1 - b) ≥ 0` gives `a ⋅ b ≤ a ≤ 1`. -/
theorem effects_mul_le_one {a b : A} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by
  have h : 0 ≤ a * (1 - b) :=
    Commute.mul_nonneg ha0 (sub_nonneg.mpr hb1) (Commute.all a (1 - b))
  rw [mul_sub, mul_one, sub_nonneg] at h
  exact h.trans ha1

/-- `[0,1]_𝒜` is closed under multiplication when `𝒜` is commutative
(`Commute.mul_nonneg` for `0 ≤ a ⋅ b`, `effects_mul_le_one` for `a ⋅ b ≤ 1`). -/
theorem effects_mul_mem (a b : Theses.effects A) :
    (a : A) * (b : A) ∈ Theses.effects A :=
  ⟨Commute.mul_nonneg a.2.1 b.2.1 (Commute.all _ _),
    effects_mul_le_one a.2.1 a.2.2 b.2.2⟩

variable [Theses.VonNeumannAlgebra A]

/-- **195V.5** (eff.tex:3275, Examples): the effect algebra `[0,1]_𝒜` of a
*commutative* von Neumann algebra is an effect monoid, with `⊙` the algebra's
own multiplication.  (A `def`, not an `instance` — exactly as
`continuousUnitIntervalEffectMonoid` is for `C(X)` — since a von Neumann
algebra's effects also carry the non-commutative sequential product of 225V.)

Everything but the multiplication is `effectsEffectAlgebra` (175II.3); the
`distrib` axiom is ring distributivity, and the three orthogonality side
conditions are `effects_mul_le_one` applied to `(a ⋁ b) ⊙ c`, `(a ⋁ b) ⊙ d`
and `(a ⋁ b) ⊙ (c ⋁ d)`. -/
noncomputable def commEffectsEffectMonoid (A : Type u) [CommCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    EffectMonoid (Theses.effects A) :=
  { effectsEffectAlgebra A with
    mul := fun a b => ⟨(a : A) * (b : A), effects_mul_mem a b⟩
    one_mul := fun a => Subtype.ext (one_mul (a : A))
    mul_one := fun a => Subtype.ext (mul_one (a : A))
    mul_assoc := fun a b c => Subtype.ext (mul_assoc (a : A) (b : A) (c : A))
    distrib := by
      intro a b c d hab hcd
      have hab' : (a : A) + (b : A) ≤ 1 := hab
      have hcd' : (c : A) + (d : A) ≤ 1 := hcd
      have hs0 : (0 : A) ≤ (a : A) + (b : A) := add_nonneg a.2.1 b.2.1
      have h1 : (a : A) * (c : A) + (b : A) * (c : A) ≤ 1 := by
        rw [← add_mul]
        exact effects_mul_le_one hs0 hab' c.2.2
      have h2 : (a : A) * (d : A) + (b : A) * (d : A) ≤ 1 := by
        rw [← add_mul]
        exact effects_mul_le_one hs0 hab' d.2.2
      have hexp : (a : A) * (c : A) + (b : A) * (c : A)
          + ((a : A) * (d : A) + (b : A) * (d : A))
          = ((a : A) + (b : A)) * ((c : A) + (d : A)) := by ring
      have h3 : (a : A) * (c : A) + (b : A) * (c : A)
          + ((a : A) * (d : A) + (b : A) * (d : A)) ≤ 1 := by
        rw [hexp]
        exact effects_mul_le_one hs0 hab' hcd'
      exact isSumOf_four _ _ _ _ _ h1 h2 h3 (Subtype.ext hexp) }

end CommEffects

/-- The algebraic order `≼` of the effect algebra `[0,1]_𝒜` is the order of
`𝒜` (the witness of `a ≼ b` being `b - a`), mirroring `unitInterval_le_iff`. -/
theorem effects_pcm_le_iff {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] (a b : Theses.effects A) :
    a ≼ b ↔ (a : A) ≤ (b : A) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    show (a : A) ≤ (a : A) + (c : A)
    exact le_add_of_nonneg_right c.2.1
  · intro h
    have hcancel : (a : A) + ((b : A) - (a : A)) = (b : A) := by abel
    refine ⟨⟨(b : A) - (a : A), sub_nonneg.mpr h, (sub_le_self _ a.2.1).trans b.2.2⟩,
      ?_, ?_⟩
    · show (a : A) + ((b : A) - (a : A)) ≤ 1
      rw [hcancel]; exact b.2.2
    · exact Subtype.ext hcancel

/-! ### (c) The division on `[0,1]_{L^∞(X, μ)}` -/

section LinftyDiv

/-- A chosen `[0,1]`-valued measurable representative of an effect of
`L^∞(X, μ)`. -/
noncomputable def linftyRep (a : Theses.effects (Linfty μ)) : X → ℝ :=
  Classical.choose (linfty_exists_unit_rep a)

/-- `linftyRep a` is measurable. -/
theorem linftyRep_measurable (a : Theses.effects (Linfty μ)) :
    Measurable (linftyRep a) := (Classical.choose_spec (linfty_exists_unit_rep a)).1

/-- `linftyRep a` is nonnegative, everywhere. -/
theorem linftyRep_nonneg (a : Theses.effects (Linfty μ)) (x : X) : 0 ≤ linftyRep a x :=
  (Classical.choose_spec (linfty_exists_unit_rep a)).2.1 x

/-- `linftyRep a` is at most `1`, everywhere. -/
theorem linftyRep_le_one (a : Theses.effects (Linfty μ)) (x : X) : linftyRep a x ≤ 1 :=
  (Classical.choose_spec (linfty_exists_unit_rep a)).2.2.1 x

/-- `linftyRep a` represents `a`. -/
theorem linftyMkR_rep (a : Theses.effects (Linfty μ)) :
    linftyMkR μ (linftyRep a) = (a : Linfty μ) :=
  (Classical.choose_spec (linfty_exists_unit_rep a)).2.2.2

/-- `linftyRep a` is bounded measurable. -/
theorem linftyRep_bddMeas (a : Theses.effects (Linfty μ)) :
    IsBoundedMeasurableReal X (linftyRep a) :=
  isBoundedMeasurableReal_of_Icc (linftyRep_measurable a) (linftyRep_nonneg a)
    (linftyRep_le_one a)

/-- Any other representative of `a` agrees with `linftyRep a` almost everywhere. -/
theorem linftyRep_ae {a : Theses.effects (Linfty μ)} {r : X → ℝ}
    (hr : IsBoundedMeasurableReal X r) (h : linftyMkR μ r = (a : Linfty μ)) :
    linftyRep a =ᵐ[μ] r :=
  (linftyMkR_eq_iff (linftyRep_bddMeas a) hr).mp ((linftyMkR_rep a).trans h.symm)

/-- The pointwise division of representatives.  This is the thesis's
`x ↦ if g x = 0 then 0 else min (f x / g x) 1`: in Lean `t / 0 = 0`, so the
case split is already built into `min (f x / g x) 1`. -/
noncomputable def linftyDivFun (a b : Theses.effects (Linfty μ)) : X → ℝ :=
  fun x => min (linftyRep a x / linftyRep b x) 1

/-- `linftyDivFun` is nonnegative. -/
theorem linftyDivFun_nonneg (a b : Theses.effects (Linfty μ)) (x : X) :
    0 ≤ linftyDivFun a b x :=
  le_min (div_nonneg (linftyRep_nonneg a x) (linftyRep_nonneg b x)) zero_le_one

/-- `linftyDivFun` is at most `1`. -/
theorem linftyDivFun_le_one (a b : Theses.effects (Linfty μ)) (x : X) :
    linftyDivFun a b x ≤ 1 := min_le_right _ _

/-- `linftyDivFun` is measurable. -/
theorem linftyDivFun_measurable (a b : Theses.effects (Linfty μ)) :
    Measurable (linftyDivFun a b) :=
  ((linftyRep_measurable a).div (linftyRep_measurable b)).min measurable_const

/-- `linftyDivFun` is bounded measurable. -/
theorem linftyDivFun_bddMeas (a b : Theses.effects (Linfty μ)) :
    IsBoundedMeasurableReal X (linftyDivFun a b) :=
  isBoundedMeasurableReal_of_Icc (linftyDivFun_measurable a b) (linftyDivFun_nonneg a b)
    (linftyDivFun_le_one a b)

/-- **195V.5** (eff.tex:3275, Examples): the partial division of
`[0,1]_{L^∞(X, μ)}`, as a total operation — the class of
`x ↦ min (a(x)/b(x)) 1`. -/
noncomputable def linftyDiv (a b : Theses.effects (Linfty μ)) :
    Theses.effects (Linfty μ) :=
  ⟨linftyMkR μ (linftyDivFun a b),
    linftyMkR_mem_effects (linftyDivFun_measurable a b) (linftyDivFun_nonneg a b)
      (linftyDivFun_le_one a b)⟩

/-- The chosen representative of `a/b` is `linftyDivFun a b` almost everywhere. -/
theorem linftyRep_div (a b : Theses.effects (Linfty μ)) :
    linftyRep (linftyDiv a b) =ᵐ[μ] linftyDivFun a b :=
  linftyRep_ae (linftyDivFun_bddMeas a b) rfl

variable [IsFiniteMeasure μ]

/-- The algebraic order of `[0,1]_{L^∞(X, μ)}` is the almost-everywhere
pointwise order of the representatives. -/
theorem linfty_pcm_le_ae {a b : Theses.effects (Linfty μ)} :
    a ≼ b ↔ ∀ᵐ x ∂μ, linftyRep a x ≤ linftyRep b x := by
  rw [effects_pcm_le_iff a b, ← linftyMkR_rep a, ← linftyMkR_rep b]
  exact linftyMkR_le_iff (linftyRep_bddMeas a) (linftyRep_bddMeas b)

attribute [local instance] commEffectsEffectMonoid

/-- **195V.5** (eff.tex:3275, Examples): the effect divisoid structure on
`[0,1]_{L^∞(X, μ)}`, with `a/b` the class of `x ↦ min (a(x)/b(x)) 1`.

All five axioms are almost-everywhere pointwise facts about `[0,1]`-valued
measurable representatives; `b/b` is the indicator of `{b ≠ 0}` (the support
projection), which is where the honest support of a measurable function
replaces the *closure* of the support that 195VI needs for `C(X)`.  The only
axiom with content is `div_unique`: from `c ≼ b/b` and `b ⊙ c = a` almost
everywhere, `c = 0 = a/b` off `{b ≠ 0}`, and `c = a/b ≤ 1` on it. -/
noncomputable def linftyEffectDivisoid (μ : Measure X) [IsFiniteMeasure μ] :
    EffectDivisoid (Theses.effects (Linfty μ)) where
  div := linftyDiv
  div_le := by
    intro a b _
    refine linfty_pcm_le_ae.mpr ?_
    filter_upwards [linftyRep_div a b, linftyRep_div b b] with x h1 h2
    rw [h1, h2]
    show min (linftyRep a x / linftyRep b x) 1 ≤ min (linftyRep b x / linftyRep b x) 1
    by_cases hb : linftyRep b x = 0
    · simp [hb]
    · rw [div_self hb, min_self]
      exact min_le_right _ _
  mul_div := by
    intro a b hab
    have hle := linfty_pcm_le_ae.mp hab
    refine Subtype.ext ?_
    show (b : Linfty μ) * linftyMkR μ (linftyDivFun a b) = (a : Linfty μ)
    rw [← linftyMkR_rep a, ← linftyMkR_rep b,
      ← linftyMkR_mul (linftyRep_bddMeas b) (linftyDivFun_bddMeas a b)]
    refine (linftyMkR_eq_iff ((linftyRep_bddMeas b).mul (linftyDivFun_bddMeas a b))
      (linftyRep_bddMeas a)).mpr ?_
    filter_upwards [hle] with x hx
    show linftyRep b x * min (linftyRep a x / linftyRep b x) 1 = linftyRep a x
    by_cases hb : linftyRep b x = 0
    · have ha : linftyRep a x = 0 := le_antisymm (hb ▸ hx) (linftyRep_nonneg a x)
      rw [hb, ha]; simp
    · have hbpos : 0 < linftyRep b x :=
        lt_of_le_of_ne (linftyRep_nonneg b x) (Ne.symm hb)
      rw [min_eq_left ((div_le_one hbpos).mpr hx)]
      field_simp
  div_unique := by
    intro a b c hab hc hmul
    have hcle := linfty_pcm_le_ae.mp hc
    have hbc : (b : Linfty μ) * (c : Linfty μ) = (a : Linfty μ) :=
      congrArg Subtype.val hmul
    rw [← linftyMkR_rep a, ← linftyMkR_rep b, ← linftyMkR_rep c,
      ← linftyMkR_mul (linftyRep_bddMeas b) (linftyRep_bddMeas c)] at hbc
    have hbc' : ∀ᵐ x ∂μ, linftyRep b x * linftyRep c x = linftyRep a x :=
      (linftyMkR_eq_iff ((linftyRep_bddMeas b).mul (linftyRep_bddMeas c))
        (linftyRep_bddMeas a)).mp hbc
    refine Subtype.ext ?_
    show (c : Linfty μ) = linftyMkR μ (linftyDivFun a b)
    rw [← linftyMkR_rep c]
    refine (linftyMkR_eq_iff (linftyRep_bddMeas c) (linftyDivFun_bddMeas a b)).mpr ?_
    filter_upwards [hcle, hbc', linftyRep_div b b] with x h2 h3 h4
    rw [h4] at h2
    show linftyRep c x = min (linftyRep a x / linftyRep b x) 1
    by_cases hb : linftyRep b x = 0
    · have h5 : linftyDivFun b b x = 0 := by
        show min (linftyRep b x / linftyRep b x) 1 = 0
        simp [hb]
      have hc0 : linftyRep c x = 0 := le_antisymm (h5 ▸ h2) (linftyRep_nonneg c x)
      rw [hc0, hb]
      simp
    · have hone : linftyDivFun b b x = 1 := by
        show min (linftyRep b x / linftyRep b x) 1 = 1
        rw [div_self hb, min_self]
      rw [hone] at h2
      have hq : linftyRep a x / linftyRep b x = linftyRep c x := by
        rw [← h3]; field_simp
      rw [hq, min_eq_left h2]
  le_div_self := by
    intro a
    refine linfty_pcm_le_ae.mpr ?_
    filter_upwards [linftyRep_div a a] with x h1
    rw [h1]
    show linftyRep a x ≤ min (linftyRep a x / linftyRep a x) 1
    by_cases ha : linftyRep a x = 0
    · simp [ha]
    · rw [div_self ha, min_self]
      exact linftyRep_le_one a x
  div_div_self := by
    intro a
    refine Subtype.ext ?_
    show linftyMkR μ (linftyDivFun (linftyDiv a a) (linftyDiv a a))
        = linftyMkR μ (linftyDivFun a a)
    refine (linftyMkR_eq_iff (linftyDivFun_bddMeas _ _)
      (linftyDivFun_bddMeas a a)).mpr ?_
    filter_upwards [linftyRep_div a a] with x h1
    show min (linftyRep (linftyDiv a a) x / linftyRep (linftyDiv a a) x) 1
        = min (linftyRep a x / linftyRep a x) 1
    rw [h1]
    by_cases ha : linftyRep a x = 0
    · simp [linftyDivFun, ha]
    · have h2 : linftyDivFun a a x = 1 := by
        show min (linftyRep a x / linftyRep a x) 1 = 1
        rw [div_self ha, min_self]
      rw [h2, div_self ha]
      norm_num

end LinftyDiv

/-- **195V.5** (eff.tex:3275, Examples), second half: the effect monoid on
the unit interval of `L^∞(X, μ)` — for any finite measure space — **is** an
effect divisoid.

195V prints no argument (the parenthetical `basic-divisoid-equiv` is 195VI,
the `C(X)` criterion, which would reach `L^∞` only through a hyperstonean
spectrum), so this is a direct construction: `commEffectsEffectMonoid` for
the multiplication, and `linftyEffectDivisoid` for the division
`a/b = [x ↦ min (a(x)/b(x)) 1]`. -/
theorem linfty_unitInterval_divisoid {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    letI := commEffectsEffectMonoid (Linfty μ)
    Nonempty (EffectDivisoid (Theses.effects (Linfty μ))) :=
  ⟨linftyEffectDivisoid μ⟩

/-- **195V.5** (eff.tex:3275, Examples), the named instance: the effect
monoid on the unit interval of `L^∞[0,1]` is an effect divisoid.

`L^∞[0,1]` is `Linfty (volume.restrict (Set.Icc 0 1))` on `ℝ`: the measure
is finite (`Restrict.isFiniteMeasure`), and functions off `[0,1]` are almost
everywhere irrelevant to it, so that measure algebra *is* the one of
`[0,1]`. -/
theorem linfty_Icc_unitInterval_divisoid :
    letI := commEffectsEffectMonoid (Linfty (volume.restrict (Set.Icc (0 : ℝ) 1)))
    Nonempty (EffectDivisoid
      (Theses.effects (Linfty (volume.restrict (Set.Icc (0 : ℝ) 1))))) :=
  linfty_unitInterval_divisoid _

end LinftyDivisoid

end Theses.B.Eff
