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
and all of `B/Dils`.  `A/Proc` is deliberately *not* imported, and nothing
proved here has needed it.  **One statement below does**: `vn_is_andthen_eff`
(211IV) is proved in eff.tex:4859 from **105V** `positive-map-uniqueness` and
**100III** `pure-fundamental`, both in `Theses/A/Proc/Measurement.lean` — and
105V is itself still `sorry` there.  So that item is blocked twice over: the
import would have to be added *and* 105V closed first.  (An earlier version of
this header claimed nothing here needs `A/Proc`; that was wrong.)

**Nothing was changed in the move**: each statement below is verbatim the
one that stood in the file named after it, same name, same binders, same
doc comment.
-/
import Theses.B.Eff.Comparisons
import Theses.B.Dils.Pure

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
sum (**55XIII**.2). -/
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

The join is `⋃{p,q}` of **56XVI** (`Theses.A.VN.projSup`, proved in thesis
A); the meet is its De Morgan dual.  Orthomodularity comes down to
**55XIII**.2, that the sum of two orthogonal projections is their *least*
upper bound among projections: for `p ≤ q` one computes `pᶜ ⊓ q = q - p`
and then `p ⊔ (q - p) = p + (q - p) = q`. -/
theorem projections_orthomodularLattice (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (OrthomodularLattice { p : A // IsStarProjection p }) := by
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
            compl_compl := ?_, orthomodular := ?_ }⟩
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

/-- **180V** (`effectus-vn`, eff.tex:827): the partial maps of the effectus
`vNᵒᵖ` correspond to the ncpsu-maps: `(W*_ncpsu)ᵒᵖ` is an effectus in
partial form (its effect object being `ℂ`). -/

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
* **real** — `μ` carries `Scal C = C(I,I)` bijectively onto `[0,1] ⊆ ℝ`,
  taking `⋁` to `+` and composition to multiplication. -/
theorem su_real_separating :
    IsRealEffectus (WStarCPSU.{u}ᵒᵖ) ∧ SeparatingPredicates (WStarCPSU.{u}ᵒᵖ) ∧
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
  refine ⟨?_, hsepP, hsepS⟩
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
  refine ⟨{ toEAHom := { toPCMHom := { toFun := s
                                       perp_map := ?_
                                       ovee_map := ?_ }
                         map_one := ?_ }
            map_mul := ?_ }, ?_, ?_⟩
  · intro k l h
    show ((s k : ℝ)) + ((s l : ℝ)) ≤ 1
    have h2 := hperp k l h
    rw [← hs, ← hs] at h2
    obtain ⟨h3, -⟩ := Complex.le_def.mp h2
    simpa using h3
  · intro k l h
    refine Subtype.ext ?_
    show ((s (ovee k l h) : ℝ)) = ((s k : ℝ)) + ((s l : ℝ))
    have h2 := hadd k l h
    rw [← hs, ← hs, ← hs] at h2
    exact_mod_cast h2
  · refine Subtype.ext ?_
    show ((s 1 : ℝ)) = 1
    have h2 := hone
    rw [← hs] at h2
    exact_mod_cast h2
  · intro k l
    refine Subtype.ext ?_
    show ((s (k * l) : ℝ)) = ((s k : ℝ)) * ((s l : ℝ))
    have h2 := hmul k l
    rw [← hs, ← hs, ← hs] at h2
    exact_mod_cast h2
  · -- injective
    intro k l hkl
    have hkl' : s k = s l := hkl
    have h2 : t k = t l := by rw [← hs, ← hs, hkl']
    have h1 : k.unop.toNCPMap (1 : effCarrier) = l.unop.toNCPMap 1 := by
      rw [← hall (k.unop.toNCPMap 1), ← hall (l.unop.toNCPMap 1), ← ht k, ← ht l,
        h2]
    exact suop_hom_ext fun a => by rw [hunop k a, hunop l a, h1]
  · -- surjective
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
effects `[0,1]_𝒜` and its states to the normal states.) -/
theorem effectus_vn_real_separating
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    IsRealEffectus WStarCPSU.{u}ᵒᵖ ∧ SeparatingPredicates WStarCPSU.{u}ᵒᵖ ∧
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
    DiamondEffectus WStarCPSU.{u}ᵒᵖ := sorry

/-- **211IV** (`vn-is-andthen-eff`, eff.tex:4859, Examples): `vNᵒᵖ` is an
&-effectus, with `asrt_a(b) = √a b √a` (as are `CvNᵒᵖ` and `EJAᵒᵖ`, not
formalized here; these are the only known examples). -/
theorem vn_is_andthen_eff (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    AndThenEffectus WStarCPSU.{u}ᵒᵖ := sorry

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
      Nonempty (DaggerEffectus WStarCPSU.{u}ᵒᵖ) := sorry

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
      HasDilations WStarCPSU.{u}ᵒᵖ := sorry

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
        IsDilation f ϱ h → DilationOrderCorrespondence f ϱ h := sorry

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
      ¬ HasBinaryCoproducts (PureCat WStarCPSU.{u}ᵒᵖ) := sorry

/-- **224VII** (`exc-purec-equal`, eff.tex:7218, Exercise\*):
`Pure (vNᵒᵖ)` does not have all coequalizers. -/
theorem exc_purec_equal (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasCoequalizers (PureCat WStarCPSU.{u}ᵒᵖ) := sorry

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
`a & b = √a b √a`. -/
theorem effects_sea (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (SequentialEffectAlgebra (Theses.effects A)) := ⟨effectsSEA⟩

end Theses.B.Eff
