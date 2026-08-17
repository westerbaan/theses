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
and all of `B/Dils`.  `A/Proc` (tensor products, the symmetric monoidal
structure) is deliberately *not* imported: nothing here has been shown to
need it.  Add it if and when a proof does.

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

/-! ## `vNᵒᵖ` is an effectus (parsec 180)

Moved from `Effectus.lean`. -/

/-- **180V** (`effectus-vn`, eff.tex:827) and **189aI**
(`effexamplesintro`, eff.tex:2020, Examples): the main example — the
opposite `vNᵒᵖ` of the category of von Neumann algebras with ncpu-maps is
an effectus in total form. -/
theorem effectus_vn : Nonempty (EffectusTotalStructure WStarNCPU.{u}ᵒᵖ) := sorry

/-- **180V** (`effectus-vn`, eff.tex:827): the partial maps of the effectus
`vNᵒᵖ` correspond to the ncpsu-maps: `(W*_ncpsu)ᵒᵖ` is an effectus in
partial form (its effect object being `ℂ`). -/
theorem effectus_vn_partial :
    Nonempty (EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) := sorry

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
      SeparatingStates WStarCPSU.{u}ᵒᵖ := sorry

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

/-- **225V** (eff.tex:7381, Examples): the effect algebra `[0,1]_𝒜` of a
von Neumann algebra is a sequential effect algebra with
`a & b = √a b √a`. -/
theorem effects_sea (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (SequentialEffectAlgebra (Theses.effects A)) := sorry

end Theses.B.Eff
