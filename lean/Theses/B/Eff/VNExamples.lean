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

The other seven files of `Theses/B/Eff/` import **only** `Theses.Common`,
which keeps the whole effectus development independent of the
`A/CStar → A/VN → {A/Proc, B/Dils}` chain: they build fast and cannot be
broken by work upstream.  Rather than give that up by importing thesis A
into `Effectus.lean`, `Dagger.lean`, … the author ruled that the
A-dependent statements move here, to a single leaf module.  Only this file
sees thesis A, and only this file is exposed to churn in it.

`Theses.B.Dils.Pure` transitively supplies all of `A/CStar`, all of `A/VN`
and all of `B/Dils`.  **`Theses.A.Proc.Measurement` is imported too**, as of
session 88: `vn_has_dilations` (221III) needs *sharp + total ⟹ nmiu*, which
eff.tex:4779 proves by citing `sharp-multiplicative` = **99XII**
(proc.tex:905), and that is proved there.  The import is cheap and safe —
`Measurement.lean` imports only `Theses.A.VN.NormalFunctionals`, which
`B/Dils` already supplies, so it adds one file and a few seconds; and it is
added **here only**, so the other eight files of `Theses/B/Eff/` still import
`Theses.Common` alone and the author ruling above is untouched.
(`Measurement.lean` carries `sorry`s of its own, but the three results used
from it — `sharp_multiplicative`, `gardner`, `pure_fundamental` — are
`#print axioms`-clean.)

`vn_is_andthen_eff` (211IV) is proved in eff.tex:4859 from **105V**
`positive-map-uniqueness` and **100III** `pure-fundamental`, both in
`Theses/A/Proc/Measurement.lean`.  As of session 91 **both are proved and
axiom-clean** there — 104VII `positive_quotients_centrally_similar`, which
105V rested on, closed in session 91 — so 211IV is no longer blocked by
anything in `A/Proc`.  What it now waits on is **QUESTIONS B15**, a
definitional mismatch between the two theses over whether the ⋄-self-adjoint
square root of a ⋄-positive map is required to be pure; see the doc comment
on `vn_is_andthen_eff` itself.
(An earlier version of this header claimed nothing here needs `A/Proc`; that
was wrong.)

**Nothing was changed in the move**: each statement below is verbatim the
one that stood in the file named after it, same name, same binders, same
doc comment.
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
which 8II of thesis A explicitly admits.  This was recorded (PROVING-LOG,
session 69) as the next gate, on the ground that "`CStarAlgebra PUnit` does
not synthesize".  It does not, but only because the four instances below are
missing from Mathlib; **`CStarAlgebra` extends `NormedRing`, not
`NormOneClass`**, so nothing about the trivial algebra is actually excluded.
(Mathlib does already have one trivial C\*-algebra by accident:
`CStarAlgebra (Π _ : Empty, ℂ)` synthesises from the finite-`Pi` instance.)

With these, `WStar.trivial` is a bona fide object of `WStarNCPU`/`WStarCPSU`.
That it is final in `vN` (hence initial in `vNᵒᵖ`) is `vnTrivIsTerminal`
below, and `suTrivIsTerminal` for the ncpsu-maps.  (`WStar.trivial` was
originally stated one universe too high — `WStar.{u+1}`, which can never be an
object of `WStarNCPU.{u}` — and is corrected here.) -/

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

Moved from `EffectAlgebras.lean`. -/

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

Moved from `Effectus.lean`. -/

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

/-- The value at `1` of an ncpsu-map out of the scalars is an effect. -/
theorem ncpsu_scal_nonneg (f : Theses.NCPSUMap (ULift.{u} ℂ) A) :
    0 ≤ f.toNCPMap 1 := by
  have h := OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap
    (show (0 : ULift.{u} ℂ) ≤ 1 from by
      show (0 : ℂ) ≤ (1 : ℂ)
      exact zero_le_one)
  rwa [map_zero] at h

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

theorem wUnitSU_one (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : (wUnitSU A).toNCPMap 1 = (1 : A) := (wUnit A).unital'

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
built above.  (`effectus_vn_partial` is its `Nonempty` form; the bundled
version is what `vn_effObj_iso` compares an arbitrary structure with.) -/
noncomputable def vnPartialStructure : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ :=
  { hasFiniteCoproducts := suHasFiniteCoproducts
    homPCM := suPCM
    finPAC := suFinPAC
    effectus := suEffectusPartialForm }

/-- **180V** (`effectus-vn`, eff.tex:827): `(W*_ncpsu)ᵒᵖ` is an effectus in
**partial form**.

⚠ **What this statement does and does not say** (audit row 180V).  The
sentence of 180V being rendered is *"the partial maps \[of `vNᵒᵖ`\]
correspond to ncp-maps `f` with `f(1) ≤ 1`"*, i.e. `Par(vNᵒᵖ) ≃ W*_ncpsuᵒᵖ`.
Two clauses of it are **not** in the statement below:

* **the effect object is `ℂ`.**  Supplied by the proof
  (`suEffectusPartialForm` builds `I = ℂᵤ`), but not asserted:
  `Nonempty (EffectusPartialStructure …)` says only that *some* structure
  exists.  Strengthening it to `∃ s, s.effectus.I = suI` costs one line and
  is **QUESTIONS B13**, which asks for a ruling; it is therefore left alone
  here.  What the eight examples downstream actually use is not this but the
  *uniqueness* statement `vn_effObj_iso`, which is proved.
* **the comparison with `Par(vNᵒᵖ)` itself.**  Nothing here relates
  `W*_ncpsuᵒᵖ` to the category of partial maps of the *total*-form effectus
  `effectus_vn`.  This is the blocker wave 1 named for four
  `StatesPredicates` rows: `Par C` needs `HasFiniteCoproducts C` and
  `HasTerminal C` as **instances**, and for `WStarNCPU.{u}ᵒᵖ` those live
  inside the proof of `effectus_vn` as a `CoprodPres` record (`vnPres`), so
  the statement would first have to hoist them and then transport along
  `⊤_ C ≅ vnPres.T` and `Y ⨿ ⊤_ C ≅ vnPres.P Y vnPres.T` before the
  hom-bijection `φ ↦ φ(·, 0)` (inverse `f ↦ ((y, λ) ↦ f(y) + λ(1 - f(1)))`)
  and its compatibility with Kleisli composition could even be stated. -/

theorem effectus_vn_partial :
    Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :=
  ⟨vnPartialStructure⟩

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

The route recorded in PROVING-LOG session 84 (cut the circle "`I` terminal in
`Tot`" by the `I`-free characterisation *total ⟺ `≼`-maximal*) is **not** the
route taken: that characterisation is false in `vN_cpsuᵒᵖ` — the unique map
`X ⟶ 0` into the initial object is `≼`-maximal but not total unless `X` is a
zero object.  What replaces it is step 4, which uses `one_m_is_id` at the
effect object itself and never mentions `Tot`. -/

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
route needs neither the pseudoinverse of `√ξ(1)` nor factoriality as such
(see `PROVING-LOG.md`, session 90). -/

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
functionals, **30IV**.1 (`omega-norm-basic`, cstar.tex:4767)
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
(**30IV**.1, `omega-norm-basic`, cstar.tex:4767, `omega_norm_basic_1`): a
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

**On the reality conjunct** (audit row 190II.3, repaired in session 94).
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
corners**, not the other way round.  (eff.tex:3686 and eff.tex:3935; the
Remarks at dils.tex:6072 and dils.tex:6140 say the same, each calling the
effectus-side notion "the direction-reversed counterpart".  The record in
`docs/BEff-survey.md` and `PROVING-LOG.md` had the two swapped.)

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
  (dils.tex 169VIII, in the form repaired under QUESTIONS **B11**, whose
  mediating map is *subunital*: precisely what a morphism of this category
  is).

Both are `Prop`-valued classes with existential fields, so no canonical
choice of corner or filter has to be made. -/

/-- **199V at `vNᵒᵖ`** (eff.tex:3933, Examples): `vN_cpsuᵒᵖ` **has
comprehension**, and a comprehension for the effect `a` is the standard
corner `h_a : 𝒜 → ⌊a⌋𝒜⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋` (dils.tex 169IV
`standard_corner_dils`). -/
private theorem su_exists_corner {X : WStarCPSU.{u}ᵒᵖ}
    (p : X ⟶ effObj (WStarCPSU.{u}ᵒᵖ)) :
    ∃ (W : WStarCPSU.{u}ᵒᵖ) (π : W ⟶ X), IsComprehension p π ∧
      suCarrier π = Theses.A.VN.floor (suPredVal p) ∧
      Function.Surjective π.unop.toNCPMap := by
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
    refine ⟨_, π, ⟨?_, ?_⟩, ?_, ?_⟩
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

/-- **199V at `vNᵒᵖ`** (eff.tex:3933, Examples): `vN_cpsuᵒᵖ` **has
comprehension**, and a comprehension for the effect `a` is the standard
corner `h_a : 𝒜 → ⌊a⌋𝒜⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋` (dils.tex 169IV
`standard_corner_dils`). -/
theorem su_hasComprehension : HasComprehension (WStarCPSU.{u}ᵒᵖ) :=
  ⟨fun p => by
    obtain ⟨W, π, hπ, -, -⟩ := su_exists_corner p
    exact ⟨W, π, hπ⟩⟩

/-- **197IV at `vNᵒᵖ`** (eff.tex:3683, Examples): `vN_cpsuᵒᵖ` **has
quotients**, and a quotient for the effect `a` is the standard filter
`c_{aᗮ} : ⌈aᗮ⌉𝒜⌈aᗮ⌉ → 𝒜`, `b ↦ √(aᗮ) b √(aᗮ)` (dils.tex 169X
`dils_stand_filter`). -/
theorem su_hasQuotients : HasQuotients (WStarCPSU.{u}ᵒᵖ) where
  quot {X} p := by
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
    refine ⟨_, ξ, ?_, ?_⟩
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
    obtain ⟨W, π, -, hcar, -⟩ := su_exists_corner p
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
one — a sharp map of `vN_cpsuᵒᵖ` need not be total.  (An earlier doc comment
here misquoted the source as "the sharp maps are exactly the nmiu-maps";
that quotation was wrong, and only the *total* half was proved.)

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
mediating map is subunital (the repair of QUESTIONS **B11**), which is
exactly a morphism, and `IsCornerFor`'s is merely ncp, which is a morphism
only because the corner is unital.

**Unitality of the corner is a real hypothesis, not a convenience.**  Under
169II as printed, `λ·h_a` is again a corner for `a` when `0 < λ < 1`
(QUESTIONS **D7**), and then the mediating map of a *subunital* `f` is
`λ⁻¹·f'`, which need not be subunital; such a corner is therefore not a
comprehension.  Every corner used below is unital, being the right leg of a
Paschke dilation of a unital map. -/

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
square.)  **211IV** `vn_is_andthen_eff` is therefore blocked on *uniqueness*
alone, i.e. on **105V** `positive-map-uniqueness` in `A/Proc`. -/
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
comprehension for `q`. -/
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

end AndThen223

/-! ### `Pure (vNᵒᵖ)` has no coequalizers (224VII)

`bsols.tex`:3480 argues with `M₄`, the swap `σ` on `ℂ²⊗ℂ²`, and the
projections `p_𝒮`, `p_𝒜` onto the symmetric and the antisymmetric subspace.
Only two properties of that configuration are used: `σ` is a self-adjoint
unitary, so `σ = 2p_𝒮 − 1`, and both `p_𝒮` and `p_𝒜 = 1 − p_𝒮` are non-zero.
The argument below is the author's, run with an arbitrary such `p` in
`B(ℋ)` — the smallest instance being `ℋ = ℂ²` with `p` a rank-one
projection, which is what `su_exc_purec_equal` uses.  Three divergences from
the printed solution, all recorded in `PROVING-LOG.md`:

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
  obtain ⟨W₀, π₀, hπ₀, -, hsurj₀⟩ := su_exists_corner q
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
universal property with the two coordinate maps of `ℂ²`.  The route below is
shorter and needs none of that machinery — see `PROVING-LOG.md`, session 90:

Write `π₁, π₂ : 𝒜 → ℂ` for the two coprojections of a hypothetical
coproduct, `a₀ = ĝ₀(1)` for the value of the mediating map of `(id, id)`
and `a₁ = ĝ₁(1)` for that of `(id, 0)`, so that `π₁(a₀) = π₂(a₀) = 1`,
`π₁(a₁) = 1` and `π₂(a₁) = 0`.  Then both `π_i` are **states** fixing `a₀`,
so `π_i(√a₀ a₁ √a₀) = π_i(a₁)` by `su_state_sqrtConj`; while
`√a₀ a₁ √a₀` lies in the range of `ĝ₀` by `su_pure_range`, on which `π₁`
and `π₂` agree — both being inverse to `ĝ₀`.  Hence `1 = π₁(a₁) = π₂(a₁)
= 0`. -/

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

/-- **224VI at `vNᵒᵖ`** (`exc-purec-no-biproduct`, eff.tex:7189, Exercise\*;
solution bsols.tex:3358): `Pure (vNᵒᵖ)` does **not** have binary
coproducts — already `ℂ` and `ℂ` have none. -/
theorem su_exc_purec_no_biproduct :
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

end PureCoequalizer

end IUnique


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

/-- **The total maps are the ncpu-maps**, for an arbitrary
`EffectusPartialStructure` on `vN_cpsuᵒᵖ`. -/
theorem vn_isTotal_iff (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ)
    {X Y : WStarCPSU.{u}ᵒᵖ} (f : X ⟶ Y) :
    (f ≫ s.effectus.one Y = s.effectus.one X) ↔ f.unop.toNCPMap 1 = 1 := by
  have : HasFiniteCoproducts (WStarCPSU.{u}ᵒᵖ) := suHasFiniteCoproducts
  have hpcm : s.homPCM = suPCM :=
    effectusPartialStructure_homPCM_unique s vnPartialStructure
  obtain ⟨hfc, pcm, hfin, E⟩ := s
  subst hpcm
  exact @su_isTotal_iff E X Y f


end Wrapper


/-! ## `vNᵒᵖ` is real, with separating states and predicates (parsec 190)

Moved from `StatesPredicates.lean`. -/

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

Moved from `DiamondAmp.lean`. -/

/-- **206III** (eff.tex:4460, Examples): `vNᵒᵖ` is a ⋄-effectus (as are
`CvNᵒᵖ`, `EJAᵒᵖ` and `Set`, not formalized here). -/
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

/-- **211IV** (`vn-is-andthen-eff`, eff.tex:4859, Examples): `vNᵒᵖ` is an
&-effectus, with `asrt_a(b) = √a b √a` (as are `CvNᵒᵖ` and `EJAᵒᵖ`, not
formalized here; these are the only known examples).

**Reduced, in session 92, to a single missing step** — see
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

What is *not* proved is the hypothesis `H` below: **eff.tex 206II.4 does
not require the ⋄-self-adjoint square root `g` of a ⋄-positive map to be
pure, where proc.tex 103I does**, so 105V is a statement about a strictly
smaller class of maps than 211II.1 quantifies over.  `H` says the two
classes agree in `vNᵒᵖ`.  It is believed true (it holds for `M₂` by a
hand computation, and it *must* hold if 211IV does, since for self-adjoint
non-positive `b` the map `ad_b` is pure and contraposed to itself with
`ad_b(1) = b²` but `ad_b ≠ ad_{|b|}`), but neither thesis proves it.
Recorded as **QUESTIONS B15**. -/
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
  refine @su_andThenEffectus_of_pure_sqrt E (@su_diamondEffectus E) ?_
  -- **the one missing step**: a ⋄-self-adjoint `g` whose square is pure has
  -- a *pure* ⋄-self-adjoint square root with the same square (QUESTIONS B15)
  intro X g hgsa hpure
  sorry

/-! ## `vNᵒᵖ` is a †-effectus, and has dilations (parsecs 215, 221, 223)

Moved from `Dagger.lean`. -/

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
(Paschke dilations; the full subcategory `CvNᵒᵖ` does not, 221IIIa — not
formalized here). -/
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

Moved from `Comparisons.lean`. -/

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

end Theses.B.Eff
