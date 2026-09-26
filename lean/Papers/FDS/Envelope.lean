/-
FDS 2.5, the clause `NRep(A**) ≅ Rep(A)` (direct_sums.tex:315).

PLAN (assessment, 2026-09-26).
* What 2.5 claims beyond `nrep_wStarCategory`: for a C*-algebra `A` with
  universal enveloping W*-algebra `A**`, `NRep(A**) ≅ Rep(A)`, "since
  non-degenerate representations of `A` extend uniquely to normal unital
  representations of `A**`".
* Route (i), constructing `A**`, is out of budget.  Mathlib has the GNS
  construction of one state (`PositiveLinearMap.GNS`) but no universal
  representation, no von Neumann bicommutant theorem, no Kaplansky density;
  the tree's von Neumann algebras are Kadison's abstract ones.  Needed:
  (a) the universal representation `⊕_ω π_ω` over all states and its
  bicommutant made a Kadison W*-algebra; (b) every representation is a
  direct sum of cyclic ones (Zorn), each unitarily equivalent to a GNS
  representation, hence quasi-contained in the universal one; (c) the
  resulting map `π_u(A)'' → B(H)` is a normal *-homomorphism (normality of
  reductions `x ↦ xp`, `p ∈ π_u(A)'`, and of direct sums); (d) uniqueness of
  the normal extension, i.e. `π_u(A)` is σ-weakly dense in its bicommutant
  (bicommutant theorem).  Estimate well over 2,500 lines.
* Route taken (faithful to the print's own justification): the print's
  parenthesis is the named hypothesis `IsRepEnvelope ι` on a unital
  *-homomorphism `ι : A → N` into a W*-algebra `N` ("every representation
  of `A` extends uniquely to a normal unital representation of `N`"), and
  from it we PROVE `NRep N ≌ Rep A`: restriction along `ι` is an
  equivalence of categories that is the identity on intertwiners (so it
  commutes with `†` and preserves the operator norm).
* Essentially surjective: the extension.  Faithful: same operators.
  Full (the one step the print leaves implicit): an intertwiner of the
  restrictions intertwines the normal representations themselves.  Proof:
  in `X ⊕ Y` the off-diagonal `T = [[0,0],[f,0]]` commutes with `ι(A)`;
  for a unitary `v` commuting with `ι(A)`, `n ↦ v ρ(n) v*` is again a
  normal extension, so by uniqueness `v` commutes with `ρ(N)`; the
  commutant of `ι(A)` is a C*-algebra spanned by its unitaries
  (`a + i√(1-a²)`, Mathlib `unitarySelfAddISMul`), so `T` commutes with
  `ρ(N)`, which says `f` intertwines.
* Unital `A` (Mathlib's `CStarAlgebra`), as in `Rep`/`rep_wStarCategory`.
-/
import Papers.FDS.DirectSums

open CategoryTheory
open scoped ComplexOrder ComplexStarModule
open Theses Theses.A.VN Complex

universe u u₁

noncomputable section

namespace Papers.FDS

section Envelope

variable {𝒜 : Type u₁} [CStarAlgebra 𝒜]
  {N : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

/-- The property the print uses of the universal enveloping W*-algebra
`A**` (direct_sums.tex:315, "non-degenerate representations of `A` extend
uniquely to normal unital representations of `A**`"): every (unital)
representation `π` of `𝒜` on a Hilbert space is `ρ ∘ ι` for exactly one
normal unital representation `ρ` of `N`.  Named hypothesis: the
construction of `A**` is in neither Mathlib nor the tree. -/
def IsRepEnvelope (ι : 𝒜 →⋆ₐ[ℂ] N) : Prop :=
  ∀ (H : HilbObj.{u}) (π : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)),
    ∃! ρ : N →⋆ₐ[ℂ] (H →L[ℂ] H), PreservesDirSups ⇑ρ ∧ ρ.comp ι = π

variable {H : HilbObj.{u}}

omit [StarOrderedRing N] in
/-- Conjugating a normal representation by a unitary keeps it normal
(conjugation is an order automorphism of `B(H)`). -/
theorem preservesDirSups_conj (ρ : N →⋆ₐ[ℂ] (H →L[ℂ] H)) (hρ : PreservesDirSups ⇑ρ)
    (v : unitary (H →L[ℂ] H)) :
    PreservesDirSups ⇑((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) v).toStarAlgHom.comp ρ) := by
  intro D s hne hdir hlub
  have h := hρ D s hne hdir hlub
  have hv1 : (v : H →L[ℂ] H) * star (v : H →L[ℂ] H) = 1 := Unitary.mul_star_self_of_mem v.2
  have hv2 : star (v : H →L[ℂ] H) * (v : H →L[ℂ] H) = 1 := Unitary.star_mul_self_of_mem v.2
  have happ : ∀ n : N, ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) v).toStarAlgHom.comp ρ) n
      = (v : H →L[ℂ] H) * ρ n * star (v : H →L[ℂ] H) := fun _ => rfl
  refine ⟨?_, fun t ht => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    show (v : H →L[ℂ] H) * ρ d * star (v : H →L[ℂ] H)
      ≤ (v : H →L[ℂ] H) * ρ s * star (v : H →L[ℂ] H)
    exact star_right_conjugate_le_conjugate (h.1 ⟨d, hd, rfl⟩) _
  · have hle : ρ s ≤ star (v : H →L[ℂ] H) * t * v := by
      refine h.2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have h1 := star_left_conjugate_le_conjugate (ht ⟨d, hd, rfl⟩) (v : H →L[ℂ] H)
      beta_reduce at h1
      rw [happ] at h1
      calc ρ d = star (v : H →L[ℂ] H) * ((v : H →L[ℂ] H) * ρ d * star (v : H →L[ℂ] H))
            * (v : H →L[ℂ] H) := by
            simp only [← mul_assoc, hv2, one_mul]
            rw [mul_assoc, hv2, mul_one]
        _ ≤ _ := h1
    have h2 := star_right_conjugate_le_conjugate hle (v : H →L[ℂ] H)
    rw [happ]
    calc (v : H →L[ℂ] H) * ρ s * star (v : H →L[ℂ] H)
        ≤ v * (star (v : H →L[ℂ] H) * t * v) * star (v : H →L[ℂ] H) := h2
      _ = t := by
        simp only [← mul_assoc, hv1, one_mul]
        rw [mul_assoc, hv1, mul_one]

variable {ι : 𝒜 →⋆ₐ[ℂ] N}

omit [StarOrderedRing N] in
/-- A unitary commuting with `ρ(ι(𝒜))` commutes with `ρ(N)`: conjugating `ρ`
by it gives another normal extension of `ρ ∘ ι`, equal to `ρ` by uniqueness. -/
theorem IsRepEnvelope.commute_unitary (hι : IsRepEnvelope ι) (ρ : N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ : PreservesDirSups ⇑ρ) (v : unitary (H →L[ℂ] H))
    (hv : ∀ a, Commute (v : H →L[ℂ] H) (ρ (ι a))) (n : N) :
    Commute (v : H →L[ℂ] H) (ρ n) := by
  have hv1 : (v : H →L[ℂ] H) * star (v : H →L[ℂ] H) = 1 := Unitary.mul_star_self_of_mem v.2
  have hv2 : star (v : H →L[ℂ] H) * (v : H →L[ℂ] H) = 1 := Unitary.star_mul_self_of_mem v.2
  obtain ⟨ρ₀, -, huniq⟩ := hι H (ρ.comp ι)
  have h1 := huniq ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) v).toStarAlgHom.comp ρ)
    ⟨preservesDirSups_conj ρ hρ v, StarAlgHom.ext fun a => by
      show (v : H →L[ℂ] H) * ρ (ι a) * star (v : H →L[ℂ] H) = ρ (ι a)
      rw [(hv a).eq, mul_assoc, hv1, mul_one]⟩
  have h2 := huniq ρ ⟨hρ, rfl⟩
  have h3 : (v : H →L[ℂ] H) * ρ n * star (v : H →L[ℂ] H) = ρ n :=
    congrArg (fun F : N →⋆ₐ[ℂ] (H →L[ℂ] H) => F n) (h1.trans h2.symm)
  show (v : H →L[ℂ] H) * ρ n = ρ n * v
  calc (v : H →L[ℂ] H) * ρ n = (v : H →L[ℂ] H) * ρ n * (star (v : H →L[ℂ] H) * v) := by
        rw [hv2, mul_one]
    _ = ((v : H →L[ℂ] H) * ρ n * star (v : H →L[ℂ] H)) * v := by simp only [mul_assoc]
    _ = ρ n * v := by rw [h3]

omit [StarOrderedRing N] in
/-- The commutant of `ρ(ι(𝒜))` commutes with `ρ(N)`, for a normal `ρ`: it is
a C*-algebra, spanned by its unitaries `a + i√(1-a²)`. -/
theorem IsRepEnvelope.commute (hι : IsRepEnvelope ι) (ρ : N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ : PreservesDirSups ⇑ρ) (T : H →L[ℂ] H) (hT : ∀ a, Commute T (ρ (ι a))) (n : N) :
    Commute T (ρ n) := by
  -- the commutant `S` of `ρ(ι(𝒜))`
  have hstar : ∀ T : H →L[ℂ] H, (∀ a, Commute T (ρ (ι a))) →
      ∀ a, Commute (star T) (ρ (ι a)) := by
    intro T hT a
    have := (hT (star a)).star_star
    rwa [map_star, map_star, star_star] at this
  -- self-adjoint elements of norm `≤ 1`
  have hsa1 : ∀ b : H →L[ℂ] H, IsSelfAdjoint b → ‖b‖ ≤ 1 → (∀ a, Commute b (ρ (ι a))) →
      Commute b (ρ n) := by
    intro b hb hnb hbS
    set w := selfAdjoint.unitarySelfAddISMul (⟨b, hb⟩ : selfAdjoint (H →L[ℂ] H)) hnb with hw
    have hwS : ∀ a, Commute (w : H →L[ℂ] H) (ρ (ι a)) := by
      intro a
      show Commute (b + I • CFC.sqrt (1 - b ^ 2)) (ρ (ι a))
      have hb2 : Commute (1 - (b : H →L[ℂ] H) ^ 2) (ρ (ι a)) :=
        (Commute.one_left _).sub_left ((hbS a).pow_left 2)
      exact (hbS a).add_left ((hb2.cfcₙ_nnreal NNReal.sqrt).smul_left I)
    have hw1 := hι.commute_unitary ρ hρ w hwS n
    have hw2 := hι.commute_unitary ρ hρ (star w) (hstar _ hwS) n
    have hre := selfAdjoint.realPart_unitarySelfAddISMul (⟨b, hb⟩ : selfAdjoint (H →L[ℂ] H)) hnb
    have hb' : b = (2⁻¹ : ℝ) • ((w : H →L[ℂ] H) + star (w : H →L[ℂ] H)) := by
      rw [← realPart_apply_coe]
      exact (congrArg Subtype.val hre).symm
    rw [hb']
    exact (hw1.add_left (by simpa using hw2)).smul_left _
  -- self-adjoint elements
  have hsa : ∀ b : H →L[ℂ] H, IsSelfAdjoint b → (∀ a, Commute b (ρ (ι a))) →
      Commute b (ρ n) := by
    intro b hb hbS
    rcases eq_or_ne b 0 with rfl | hb0
    · exact Commute.zero_left _
    have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    have hc := hsa1 (‖b‖⁻¹ • b) ((IsSelfAdjoint.all ‖b‖⁻¹).smul hb) (by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']) fun a =>
      (hbS a).smul_left _
    have : b = ‖b‖ • (‖b‖⁻¹ • b) := by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [this]
    exact hc.smul_left _
  -- general elements: real and imaginary parts
  have hre : ∀ a, Commute ((ℜ T : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) (ρ (ι a)) := by
    intro a
    rw [realPart_apply_coe]
    exact ((hT a).add_left (hstar T hT a)).smul_left _
  have him : ∀ a, Commute ((ℑ T : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) (ρ (ι a)) := by
    intro a
    rw [imaginaryPart_apply_coe]
    exact (((hT a).sub_left (hstar T hT a)).smul_left _).smul_left _
  rw [← realPart_add_I_smul_imaginaryPart T]
  exact (hsa _ (ℜ T).2 hre).add_left ((hsa _ (ℑ T).2 him).smul_left I)

/-- The first projection `H ⊕ K → H`. -/
def fstCLM (H K : HilbObj.{u}) : H.prod K →L[ℂ] H :=
  (ContinuousLinearMap.fst ℂ H K).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap

/-- An intertwiner between the restrictions to `𝒜` of two normal
representations of `N` intertwines the representations themselves: the
off-diagonal operator `[[0,0],[f,0]]` on `X ⊕ Y` lies in the commutant of
`ι(𝒜)`, hence (`IsRepEnvelope.commute`) of the normal `X ⊕ Y`. -/
theorem IsRepEnvelope.intertwines [VonNeumannAlgebra N] (hι : IsRepEnvelope ι)
    {X Y : RepObj.{u, u} N} (hX : X.IsNormal N) (hY : Y.IsNormal N) (f : X.hs →L[ℂ] Y.hs)
    (hf : ∀ a, f.comp (X.π (ι a)) = (Y.π (ι a)).comp f) (n : N) :
    f.comp (X.π n) = (Y.π n).comp f := by
  set T : X.hs.prod Y.hs →L[ℂ] X.hs.prod Y.hs :=
    (inrCLM X.hs Y.hs).comp (f.comp (fstCLM X.hs Y.hs)) with hTdef
  have hT : ∀ a, Commute T (prodRep X Y (ι a)) := by
    intro a
    refine ContinuousLinearMap.ext fun z => ?_
    have hfz := congrArg (fun F : X.hs →L[ℂ] Y.hs => F (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).1)
      (hf a)
    simp only [ContinuousLinearMap.comp_apply] at hfz
    show (WithLp.toLp 2 (0, f (X.π (ι a) (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).1))
        : WithLp 2 (X.hs × Y.hs))
      = WithLp.toLp 2 (X.π (ι a) 0, Y.π (ι a) (f (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).1))
    rw [hfz, map_zero]
  have hc := hι.commute (prodRep X Y) (hX.prod hY) T hT n
  refine ContinuousLinearMap.ext fun x => ?_
  have h := congrArg (fun z : X.hs.prod Y.hs => (WithLp.ofLp (z : WithLp 2 (X.hs × Y.hs))).2)
    (congrArg (fun F : X.hs.prod Y.hs →L[ℂ] X.hs.prod Y.hs => F (inlCLM X.hs Y.hs x)) hc.eq)
  exact h

variable (ι) in
/-- Restriction along `ι : 𝒜 → N`: a normal representation `ρ` of `N` gives
the representation `ρ ∘ ι` of `𝒜`; intertwiners are kept as they are. -/
def restrictRep : NRep N ⥤ Rep.{u₁, u} 𝒜 where
  obj X := (⟨⟨X.1.hs, X.1.π.comp ι⟩, trivial⟩ : {_X : RepObj.{u, u₁} 𝒜 // True})
  map {X Y} f :=
    let g : (repData N (RepObj.IsNormal N)).Hom X Y := f
    ⟨g.val, fun a => g.mem (ι a)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **FDS 2.5** (`nrep_ex`, direct_sums.tex:315, Example), the clause
`NRep(A**) ≅ Rep(A)`: for a unital `*`-homomorphism `ι : 𝒜 → N` into a
W*-algebra along which every representation of `𝒜` extends uniquely to a
normal unital representation of `N` (the print's reason, the named
hypothesis `IsRepEnvelope ι`, which the universal enveloping W*-algebra
`A**` satisfies), restriction along `ι` is an equivalence
`NRep N ≌ Rep 𝒜`; it is the identity on intertwiners, so it commutes with
`†` and preserves the operator norm. -/
theorem nrep_equiv_rep [VonNeumannAlgebra N] (hι : IsRepEnvelope ι) :
    (restrictRep ι).IsEquivalence ∧
      (∀ {X Y : NRep N} (f : X ⟶ Y), (restrictRep ι).map f† = ((restrictRep ι).map f)†) ∧
      (∀ {X Y : NRep N} (f : X ⟶ Y), ‖(restrictRep ι).map f‖ = ‖f‖) := by
  refine ⟨⟨?_, ?_, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · refine ⟨fun {X Y} f g h => ?_⟩
    have h' := congrArg (fun k : (repData 𝒜 fun _ => True).Hom ((restrictRep ι).obj X)
      ((restrictRep ι).obj Y) => k.val) h
    exact ConcreteStarCat.Hom.ext h'
  · refine ⟨fun {X Y} g => ?_⟩
    let g' : (repData 𝒜 fun _ => True).Hom ((restrictRep ι).obj X) ((restrictRep ι).obj Y) := g
    exact ⟨⟨g'.val, hι.intertwines X.2 Y.2 _ g'.mem⟩, rfl⟩
  · refine ⟨fun Y => ?_⟩
    obtain ⟨⟨hs, π⟩, t⟩ := Y
    obtain ⟨ρ, ⟨hρ, hcomp⟩, -⟩ := hι hs π
    refine ⟨(⟨⟨hs, ρ⟩, hρ⟩ : {X : RepObj.{u, u} N // X.IsNormal N}), ⟨eqToIso ?_⟩⟩
    subst hcomp
    rfl

/-- Sanity check that the hypothesis `IsRepEnvelope` is satisfiable: `ℂ` is
its own enveloping W*-algebra (every unital representation `c ↦ c·1` of
`ℂ` is normal, theses `starAlgHom_preservesDirSups_of_vectors`, and is the
only one). -/
theorem isRepEnvelope_complex : IsRepEnvelope (StarAlgHom.id ℂ ℂ) := by
  intro H π
  have hπ : ∀ c : ℂ, π c = c • (1 : H →L[ℂ] H) := fun c => by
    rw [← Algebra.algebraMap_eq_smul_one, ← AlgHomClass.commutes π c]; rfl
  refine ⟨π, ⟨?_, rfl⟩, fun ρ hρ => (StarAlgHom.comp_id ρ).symm.trans hρ.2⟩
  refine starAlgHom_preservesDirSups_of_vectors π Set.univ
    (fun R hR => ContinuousLinearMap.ext fun y => hR y trivial)
    fun y _ => ⟨smulNP (sq_nonneg ‖y‖) complexIdNP, fun c => ?_⟩
  rw [hπ c, smulNP_apply]
  show inner ℂ y (c • y) = ((‖y‖ ^ 2 : ℝ) : ℂ) * c
  rw [inner_smul_right,
    inner_self_eq_norm_sq_to_K, mul_comm]
  first
    | rfl
    | (push_cast; rfl)

end Envelope

end Papers.FDS
