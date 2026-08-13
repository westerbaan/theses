/-
Theses/B/Eff/Comparisons.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
7119–8137 (end of chapter): comparisons of †-effectuses with structures
from the literature — dagger kernel categories (parsec 224), sequential
effect algebras (225), and Grandis' homological categories with the Snake
Lemma (226–228).

Design:
* †-mono/†-epi/†-partial isometries/†-kernels are defined for a general
  `DaggerCat`; the results about `Pure C` for a †-effectus `C` are stated
  with the †'-form (`DaggerPrimeEffectus`, equivalent by 215III) or with
  an explicit `DaggerEffectus` structure where the dagger itself occurs.
* The homological notions (kernel order, exact maps, exactness of a
  composable pair) are defined directly in the effectus with its
  PCM-enrichment zero maps; Grandis' `Nsb A` and the transfer maps
  `f_*, f^*` are *not* formalized separately — following 227III, sharp
  predicates and `f_⋄, f^□` are used in their stead, exactly as the
  thesis itself does in the Snake Lemma 228II.
* Not separately formalized: the introductory comparisons 224I/225I–III
  (Gudder–Latrémolière axioms), the summarizing remarks 224VIII/224VIIIa
  (Tull's phased biproducts) and 228IX, and the `Nsb`-side of
  227II–227IV.
-/
import Theses.B.Eff.Dagger

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

/-! ## Dagger kernel categories (parsec 224) -/

section DaggerKernel

variable {D : Type u} [Category.{v} D] [DaggerCat D]

/-- **224II** (eff.tex:7138, Definition): in a †-category, `f` is
**†-mono** when `f† ∘ f = id`. -/
def DaggerCat.DagMono {X Y : D} (f : X ⟶ Y) : Prop :=
  f ≫ DaggerCat.dag f = 𝟙 X

/-- **224II** (eff.tex:7138, Definition): dually, `f` is **†-epi** when
`f ∘ f† = id`. -/
def DaggerCat.DagEpi {X Y : D} (f : X ⟶ Y) : Prop :=
  DaggerCat.dag f ≫ f = 𝟙 Y

/-- **224II** (eff.tex:7147, Definition): `f` is a **†-partial isometry**
when `f = m ∘ e` for a †-mono `m` and †-epi `e`. -/
def DaggerCat.DagPartialIsometry {X Y : D} (f : X ⟶ Y) : Prop :=
  ∃ (Z : D) (e : X ⟶ Z) (m : Z ⟶ Y),
    DaggerCat.DagEpi e ∧ DaggerCat.DagMono m ∧ f = e ≫ m

/-- **224II** (eff.tex:7153, Definition): a **†-kernel** of `f` is an
equalizer of `f` with `0` which is †-mono; a **†-kernel category** is a
†-category with a zero object in which every arrow has a †-kernel. -/
class DaggerKernelCategory (D : Type u) [Category.{v} D] [DaggerCat D]
    [HasZeroObject D] [HasZeroMorphisms D] : Prop where
  dagKernel : ∀ {X Y : D} (f : X ⟶ Y),
    ∃ (W : D) (k : W ⟶ X), DaggerCat.DagMono k ∧ k ≫ f = 0 ∧
      ∀ ⦃Z : D⦄ (g : Z ⟶ X), g ≫ f = 0 → ∃! g' : Z ⟶ W, g' ≫ k = g

end DaggerKernel

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

section PureDaggerKernel

variable [AndThenEffectus C]

/-- The zero maps of an effectus are pure (used to speak of zero morphisms
in `Pure C`; implicit in 224III). -/
theorem isPure_zero {X Y : C} : IsPure (0 : X ⟶ Y) :=
  ⟨⊥_ C, 0, 0, 1, 0, quotient_basics_4 _, compr_basics_4 _,
    (FinPAC.zero_comp _).symm⟩

/-- Helper for 224III (the first computation of eff.tex:7169): in a
†-effectus `f† ∘ f = asrt_{p&p}` where `p = 1 ∘ f`, since
`f = π_{im f} ∘ α ∘ ζ_{⌈p⌉} ∘ asrt_p` and
`f† = asrt_p ∘ π_{⌈p⌉} ∘ α⁻¹ ∘ ζ_{im f}` (`isDaggerOf_dag`), and
`asrt_p ∘ asrt_{⌈p⌉} ∘ asrt_p = asrt_p² ` by `asrt-absorp-rule`. -/
theorem dag_comp_dag_self (d : DaggerEffectus C) {P Q : PureCat C} (f : P ⟶ Q) :
    f.1 ≫ (d.daggerCat.dag f).1 =
      asrt (andThen (f.1 ≫ truth Q.base) (f.1 ≫ truth Q.base)) := by
  obtain ⟨α, hf, hg⟩ := isDaggerOf_dag d f
  have habs : asrt (f.1 ≫ truth Q.base) ≫
      asrt (ceilPred (f.1 ≫ truth Q.base)) = asrt (f.1 ≫ truth Q.base) :=
    (asrt_absorp_rule (asrt (f.1 ≫ truth Q.base))
      (isSharp_ceil (f.1 ≫ truth Q.base)) (isSharp_one P.base)).1.mp
      (by rw [imPred_asrt]; exact pcm_preorder_refl _)
  have key : f.1 ≫ (d.daggerCat.dag f).1 =
      (asrt (f.1 ≫ truth Q.base) ≫
        zetaMap (ceilPred (f.1 ≫ truth Q.base)) (isSharp_ceil _) ≫ α.hom ≫
        comprMap (imPred f.1)) ≫
      (zetaMap (imPred f.1) (isSharp_imPred C f.1) ≫ α.inv ≫
        comprMap (ceilPred (f.1 ≫ truth Q.base)) ≫
        asrt (f.1 ≫ truth Q.base)) := by
    rw [← hf, ← hg]
  rw [key]
  simp only [Category.assoc]
  rw [← Category.assoc (comprMap (imPred f.1))
      (zetaMap (imPred f.1) (isSharp_imPred C f.1)) _,
    (zetaMap_spec (imPred f.1) (isSharp_imPred C f.1)).2.1, Category.id_comp,
    ← Category.assoc α.hom α.inv _, α.hom_inv_id, Category.id_comp,
    ← Category.assoc (zetaMap (ceilPred (f.1 ≫ truth Q.base)) (isSharp_ceil _))
      (comprMap (ceilPred (f.1 ≫ truth Q.base))) _,
    (zetaMap_spec (ceilPred (f.1 ≫ truth Q.base)) (isSharp_ceil _)).2.2,
    ← Category.assoc, habs, andthen_square_rule]

/-- **224III.1** (eff.tex:7162, Proposition): in `Pure C` for a †-effectus
`C`, a map is †-mono iff it is a comprehension. -/
theorem pure_dagMono_iff_compr (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagMono f ↔ ∃ p : Pred Q.base, IsComprehension p f.1) := by
  show (f ≫ d.daggerCat.dag f = 𝟙 P) ↔ ∃ p : Pred Q.base, IsComprehension p f.1
  constructor
  · intro hm
    -- `id = f† ∘ f = asrt_{p&p}`, so `p & p = 1 = 1 & 1`, whence `p = 1` (216III)
    have h1 : asrt (andThen (f.1 ≫ truth Q.base) (f.1 ≫ truth Q.base)) =
        𝟙 P.base := (dag_comp_dag_self d f).symm.trans (congrArg Subtype.val hm)
    have h2 : andThen (f.1 ≫ truth Q.base) (f.1 ≫ truth Q.base) = 1 := by
      have h := (asrt_spec (andThen (f.1 ≫ truth Q.base)
        (f.1 ≫ truth Q.base))).2
      rw [h1, Category.id_comp] at h
      exact h.symm
    have h3 : andThen (1 : Pred P.base) (1 : Pred P.base) = 1 := by
      show asrt (1 : Pred P.base) ≫ (1 : Pred P.base) = 1
      rw [asrt_one, Category.id_comp]
    have hr : f.1 ≫ truth Q.base = 1 :=
      (dagger_eff_square_root d (1 : Pred P.base)).unique h2 h3
    -- so `f = π_{im f} ∘ β ∘ ζ_1` with `ζ_1` an iso: a comprehension
    obtain ⟨β, hβ⟩ := standard_form_of_eq f.2 (isSharp_one P.base)
      (isSharp_imPred C f.1) (by rw [hr]; exact ceil_of_isSharp (isSharp_one _))
      rfl
    have hasrt1 : asrt (f.1 ≫ truth Q.base) = 𝟙 P.base := by
      rw [hr]; exact asrt_one P.base
    rw [hasrt1, Category.id_comp] at hβ
    obtain ⟨-, hπζ1, hζπ1⟩ := zetaMap_spec (1 : Pred P.base) (isSharp_one _)
    haveI : IsIso (zetaMap (1 : Pred P.base) (isSharp_one _)) :=
      ⟨comprMap (1 : Pred P.base), by rw [hζπ1, asrt_one], hπζ1⟩
    refine ⟨imPred f.1, ?_⟩
    have hc : IsComprehension (imPred f.1)
        (zetaMap (1 : Pred P.base) (isSharp_one P.base) ≫ β.hom ≫
          comprMap (imPred f.1)) := by
      rw [← Category.assoc]
      exact compr_basics_1 (isComprehension_comprMap (imPred f.1))
        (zetaMap (1 : Pred P.base) (isSharp_one P.base) ≫ β.hom)
    rwa [← hβ] at hc
  · rintro ⟨p, hp⟩
    -- comprehensions are total, so `f† ∘ f = asrt_{1 & 1} = asrt_1 = id`
    have h3 : andThen (f.1 ≫ truth Q.base) (f.1 ≫ truth Q.base) = 1 := by
      have ht : f.1 ≫ truth Q.base = (1 : Pred P.base) := compr_total hp
      rw [ht]
      show asrt (1 : Pred P.base) ≫ (1 : Pred P.base) = 1
      rw [asrt_one, Category.id_comp]
    refine Subtype.ext ?_
    show f.1 ≫ (d.daggerCat.dag f).1 = 𝟙 P.base
    rw [dag_comp_dag_self d f, h3, asrt_one]

/-- **224III.1** (eff.tex:7162, Proposition), dually: a map of `Pure C` is
†-epi iff it is a quotient for a sharp predicate. -/
theorem pure_dagEpi_iff_quot (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagEpi f ↔
      ∃ s : Pred P.base, IsSharp s ∧ IsQuotient s f.1) := by
  show (d.daggerCat.dag f ≫ f = 𝟙 Q) ↔
    ∃ s : Pred P.base, IsSharp s ∧ IsQuotient s f.1
  constructor
  · intro he
    -- `f` is †-epi iff `f†` is †-mono, hence (224III.1) a comprehension
    have hm : @DaggerCat.DagMono _ _ d.daggerCat _ _ (d.daggerCat.dag f) := by
      show d.daggerCat.dag f ≫ d.daggerCat.dag (d.daggerCat.dag f) = 𝟙 Q
      rw [d.daggerCat.dag_dag]; exact he
    obtain ⟨p, hp⟩ := (pure_dagMono_iff_compr d (d.daggerCat.dag f)).mp hm
    have ht : IsSharp (imPred (d.daggerCat.dag f).1) := isSharp_imPred C _
    obtain ⟨θ, hθ, hθc, -⟩ := compr_basics_2 (isComprehension_imPred hp)
      (isComprehension_comprMap (imPred (d.daggerCat.dag f).1))
    haveI := hθ
    -- so `f = f†† = (θ ∘ π_t)† = ζ_t ∘ θ⁻¹` is a quotient for `tᵖ`
    obtain ⟨Θ, hΘ⟩ : ∃ h : Q ⟶
        PureCat.of (comprObj (imPred (d.daggerCat.dag f).1)),
      h = ⟨θ, isPure_of_isQuotient (quotient_basics_3 θ)⟩ := ⟨_, rfl⟩
    obtain ⟨Pt, hPt⟩ : ∃ h :
        (PureCat.of (comprObj (imPred (d.daggerCat.dag f).1)) : PureCat C) ⟶ P,
      h = ⟨comprMap (imPred (d.daggerCat.dag f).1),
        isPure_comprehension C (isComprehension_comprMap _)⟩ := ⟨_, rfl⟩
    have hEq : d.daggerCat.dag f = Θ ≫ Pt := by
      refine Subtype.ext ?_
      rw [hΘ, hPt]
      exact hθc.symm
    have hdΘ : d.daggerCat.dag Θ =
        ⟨inv θ, isPure_of_isQuotient (quotient_basics_3 (inv θ))⟩ := by
      rw [hΘ]
      have h := dagger_of_iso d (P := Q)
        (Q := PureCat.of (comprObj (imPred (d.daggerCat.dag f).1)))
        ⟨⟨θ, isPure_of_isQuotient (quotient_basics_3 θ)⟩,
          ⟨inv θ, isPure_of_isQuotient (quotient_basics_3 (inv θ))⟩,
          Subtype.ext (IsIso.hom_inv_id θ), Subtype.ext (IsIso.inv_hom_id θ)⟩
      exact h
    have hdPt : d.daggerCat.dag Pt =
        ⟨zetaMap (imPred (d.daggerCat.dag f).1) ht,
          isPure_of_isQuotient
            (zetaMap_spec (imPred (d.daggerCat.dag f).1) ht).1⟩ := by
      rw [hPt]; exact dagger_of_compr d ht
    have hfeq : f.1 = zetaMap (imPred (d.daggerCat.dag f).1) ht ≫ inv θ := by
      have h := congrArg d.daggerCat.dag hEq
      rw [d.daggerCat.dag_comp, d.daggerCat.dag_dag, hdΘ, hdPt] at h
      exact congrArg Subtype.val h
    refine ⟨orth (imPred (d.daggerCat.dag f).1),
      DiamondEffectus.orth_sharp ht, ?_⟩
    rw [hfeq]
    exact quotient_basics_1
      (zetaMap_spec (imPred (d.daggerCat.dag f).1) ht).1 (inv θ)
  · rintro ⟨s, hs, hq⟩
    -- `f = ζ_{sᵖ} ∘ θ⁻¹`, so `f† = θ⁻¹ ∘ π_{sᵖ}` is a comprehension
    have hos : IsSharp (orth s) := DiamondEffectus.orth_sharp hs
    have hzq : IsQuotient s (zetaMap (orth s) hos) := by
      have h := (zetaMap_spec (orth s) hos).1
      rwa [eabasics_orth_orth] at h
    obtain ⟨θ, hθ, hθc, -⟩ := quotient_basics_2 hq hzq
    haveI := hθ
    obtain ⟨Zs, hZs⟩ : ∃ h : P ⟶ PureCat.of (comprObj (orth s)),
      h = ⟨zetaMap (orth s) hos,
        isPure_of_isQuotient (zetaMap_spec (orth s) hos).1⟩ := ⟨_, rfl⟩
    obtain ⟨Θ, hΘ⟩ : ∃ h : (PureCat.of (comprObj (orth s)) : PureCat C) ⟶ Q,
      h = ⟨θ, isPure_of_isQuotient (quotient_basics_3 θ)⟩ := ⟨_, rfl⟩
    have hEq : f = Zs ≫ Θ := by
      refine Subtype.ext ?_
      rw [hZs, hΘ]
      exact hθc.symm
    have hdZs : d.daggerCat.dag Zs =
        ⟨comprMap (orth s),
          isPure_comprehension C (isComprehension_comprMap _)⟩ := by
      rw [hZs]; exact dagger_of_zeta d hos
    have hdΘ : d.daggerCat.dag Θ =
        ⟨inv θ, isPure_of_isQuotient (quotient_basics_3 (inv θ))⟩ := by
      rw [hΘ]
      have h := dagger_of_iso d (P := PureCat.of (comprObj (orth s))) (Q := Q)
        ⟨⟨θ, isPure_of_isQuotient (quotient_basics_3 θ)⟩,
          ⟨inv θ, isPure_of_isQuotient (quotient_basics_3 (inv θ))⟩,
          Subtype.ext (IsIso.hom_inv_id θ), Subtype.ext (IsIso.inv_hom_id θ)⟩
      exact h
    have hdf : (d.daggerCat.dag f).1 = inv θ ≫ comprMap (orth s) := by
      have h := congrArg d.daggerCat.dag hEq
      rw [d.daggerCat.dag_comp, hdZs, hdΘ] at h
      exact congrArg Subtype.val h
    have hm : @DaggerCat.DagMono _ _ d.daggerCat _ _ (d.daggerCat.dag f) := by
      refine (pure_dagMono_iff_compr d (d.daggerCat.dag f)).mpr ⟨orth s, ?_⟩
      rw [hdf]
      exact compr_basics_1 (isComprehension_comprMap (orth s)) (inv θ)
    have hm2 : d.daggerCat.dag f ≫
      d.daggerCat.dag (d.daggerCat.dag f) = 𝟙 Q := hm
    rwa [d.daggerCat.dag_dag] at hm2

/-- **224III.2** (eff.tex:7162, Proposition): the †-partial isometries of
`Pure C` are exactly the pristine maps. -/
theorem pure_dagPartialIsometry_iff_pristine (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagPartialIsometry f ↔ Pristine f.1) := by
  show (∃ (Z : PureCat C) (e : P ⟶ Z) (m : Z ⟶ Q),
      @DaggerCat.DagEpi _ _ d.daggerCat _ _ e ∧
      @DaggerCat.DagMono _ _ d.daggerCat _ _ m ∧ f = e ≫ m) ↔ Pristine f.1
  constructor
  · rintro ⟨Z, e, m, he, hm, rfl⟩
    -- `1 ∘ (m ∘ e) = 1 ∘ e = sᵖ` is sharp, as `m` is total
    obtain ⟨s, hs, hqe⟩ := (pure_dagEpi_iff_quot d e).mp he
    obtain ⟨q, hcm⟩ := (pure_dagMono_iff_compr d m).mp hm
    refine ⟨(e ≫ m).2, ?_⟩
    have h1 : (e ≫ m).1 ≫ truth Q.base = orth s := by
      show (e.1 ≫ m.1) ≫ truth Q.base = orth s
      rw [Category.assoc,
        show m.1 ≫ truth Q.base = truth Z.base from compr_total hcm]
      exact quotient_basics_5 hqe
    rw [h1]
    exact DiamondEffectus.orth_sharp hs
  · rintro ⟨-, hp⟩
    -- `1 ∘ f` sharp, so `asrt_{1∘f} ∘ ζ_{1∘f} = ζ_{1∘f}` and the standard
    -- form reads `f = π_{im f} ∘ β ∘ ζ_{1∘f}`
    obtain ⟨β, hβ⟩ := standard_form_of_eq f.2 hp (isSharp_imPred C f.1)
      (ceil_of_isSharp hp) rfl
    obtain ⟨hqp, hπζ, hζπ⟩ := zetaMap_spec (f.1 ≫ truth Q.base) hp
    have haz : asrt (f.1 ≫ truth Q.base) ≫ zetaMap (f.1 ≫ truth Q.base) hp =
        zetaMap (f.1 ≫ truth Q.base) hp := by
      rw [← hζπ, Category.assoc, hπζ, Category.comp_id]
    rw [← Category.assoc, haz] at hβ
    have hepure : IsPure (zetaMap (f.1 ≫ truth Q.base) hp ≫ β.hom) :=
      upm_closed_pure (isPure_of_isQuotient hqp)
        (isPure_of_isQuotient (quotient_basics_3 β.hom))
    refine ⟨PureCat.of (comprObj (imPred f.1)),
      ⟨zetaMap (f.1 ≫ truth Q.base) hp ≫ β.hom, hepure⟩,
      ⟨comprMap (imPred f.1),
        isPure_comprehension C (isComprehension_comprMap _)⟩, ?_, ?_, ?_⟩
    · exact (pure_dagEpi_iff_quot d _).mpr
        ⟨orth (f.1 ≫ truth Q.base), DiamondEffectus.orth_sharp hp,
          quotient_basics_1 hqp β.hom⟩
    · exact (pure_dagMono_iff_compr d _).mpr
        ⟨imPred f.1, isComprehension_comprMap _⟩
    · refine Subtype.ext ?_
      show f.1 = (zetaMap (f.1 ≫ truth Q.base) hp ≫ β.hom) ≫
        comprMap (imPred f.1)
      rw [Category.assoc]
      exact hβ

/-- **224III** (eff.tex:7173, Proposition): `Pure C` is a †-kernel
category: the †-kernel of `f` is given by the comprehension
`π_{(1∘f)ᵖ}`. -/
theorem pure_daggerKernelCategory (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    ∃ (W : PureCat C) (k : W ⟶ P),
      DaggerCat.DagMono k ∧
      IsComprehension (orth (f.1 ≫ truth Q.base)) k.1 ∧
      k.1 ≫ f.1 = 0 ∧
      ∀ ⦃Z : PureCat C⦄ (g : Z ⟶ P), g.1 ≫ f.1 = 0 →
        ∃! g' : Z ⟶ W, g' ≫ k = g := by
  haveI := dagger_thm_necessity d
  set p := f.1 ≫ truth Q.base with hpdef
  have hk : IsPure (comprMap (orth p)) :=
    isPure_comprehension C (isComprehension_comprMap _)
  have hks : IsSharp (imPred (comprMap (orth p))) := isSharp_imPred C _
  refine ⟨PureCat.of (comprObj (orth p)), ⟨comprMap (orth p), hk⟩, ?_,
    isComprehension_comprMap _, ?_, ?_⟩
  · exact (pure_dagMono_iff_compr d _).mpr ⟨_, isComprehension_comprMap _⟩
  · -- `pᵖ ∘ π_{pᵖ} = 1 ∘ π_{pᵖ}`, so `1 ∘ f ∘ π_{pᵖ} = 0` and `f ∘ π_{pᵖ} = 0`
    refine EffectusPartialForm.eq_zero_of_one_zero ?_
    show (comprMap (orth p) ≫ f.1) ≫ truth Q.base = 0
    rw [Category.assoc, ← hpdef]
    have h := compr_basics_6 (isComprehension_comprMap (orth p))
    rwa [eabasics_orth_orth] at h
  · intro Z g hg
    -- `1 ∘ f ∘ g = 0`, so `g` factors through `π_{pᵖ}`, whence `im g ≤ im π_{pᵖ}`
    have hgp : g.1 ≫ p = 0 := by rw [hpdef, ← Category.assoc, hg, FinPAC.zero_comp]
    have hgo : g.1 ≫ orth p = g.1 ≫ truth P.base := by
      refine (comp_orth_eq_zero_iff g.1 (orth p)).mp ?_
      rw [eabasics_orth_orth]; exact hgp
    obtain ⟨g0, hg0, -⟩ := (isComprehension_comprMap (orth p)).2 g.1 hgo
    have himg : imPred g.1 ≼ imPred (comprMap (orth p)) := by
      rw [← hg0]
      exact (im_ineq (comprMap (orth p)) g0).1
    have habs : g.1 ≫ asrt (imPred (comprMap (orth p))) = g.1 :=
      (asrt_absorp_rule g.1 hks (isSharp_one Z.base)).1.mp himg
    -- `π_{pᵖ}` is pristine, so `π_{pᵖ}† ∘ π_{pᵖ} = asrt_{im π_{pᵖ}}`
    have hkpr : Pristine (comprMap (orth p)) := by
      refine ⟨hk, ?_⟩
      rw [show comprMap (orth p) ≫ truth P.base = truth (comprObj (orth p)) from
        compr_total (isComprehension_comprMap _)]
      exact isSharp_one _
    have hsq : andThen (imPred (comprMap (orth p))) (imPred (comprMap (orth p))) =
        imPred (comprMap (orth p)) := by
      have h := asrt_ceil_comp (imPred (comprMap (orth p)))
      rwa [ceil_of_isSharp hks] at h
    have hdd : (d.daggerCat.dag
          (⟨comprMap (orth p), hk⟩ :
            PureCat.of (comprObj (orth p)) ⟶ P)).1 ≫
        truth (comprObj (orth p)) = imPred (comprMap (orth p)) := by
      rw [dag_eq_pureDagger d _]
      exact pristine_dagger_truth hkpr
    have hkk : (d.daggerCat.dag
          (⟨comprMap (orth p), hk⟩ :
            PureCat.of (comprObj (orth p)) ⟶ P)).1 ≫ comprMap (orth p) =
        asrt (imPred (comprMap (orth p))) := by
      have h := dag_comp_dag_self d (d.daggerCat.dag
        (⟨comprMap (orth p), hk⟩ : PureCat.of (comprObj (orth p)) ⟶ P))
      rw [d.daggerCat.dag_dag] at h
      refine h.trans ?_
      congr 1
      show andThen ((d.daggerCat.dag
          (⟨comprMap (orth p), hk⟩ :
            PureCat.of (comprObj (orth p)) ⟶ P)).1 ≫ truth (comprObj (orth p)))
        ((d.daggerCat.dag
          (⟨comprMap (orth p), hk⟩ :
            PureCat.of (comprObj (orth p)) ⟶ P)).1 ≫
            truth (comprObj (orth p))) = imPred (comprMap (orth p))
      rw [hdd, hsq]
    refine ⟨g ≫ d.daggerCat.dag ⟨comprMap (orth p), hk⟩, ?_, ?_⟩
    · refine Subtype.ext ?_
      show (g.1 ≫ (d.daggerCat.dag
        (⟨comprMap (orth p), hk⟩ :
          PureCat.of (comprObj (orth p)) ⟶ P)).1) ≫ comprMap (orth p) = g.1
      rw [Category.assoc, hkk, habs]
    · intro g'' hg''
      haveI : Mono (comprMap (orth p)) :=
        compr_basics_5 (isComprehension_comprMap (orth p))
      refine Subtype.ext ((cancel_mono (comprMap (orth p))).mp ?_)
      have e1 : g''.1 ≫ comprMap (orth p) = g.1 := congrArg Subtype.val hg''
      rw [e1]
      show g.1 = (g.1 ≫ (d.daggerCat.dag
        (⟨comprMap (orth p), hk⟩ :
          PureCat.of (comprObj (orth p)) ⟶ P)).1) ≫ comprMap (orth p)
      rw [Category.assoc, hkk, habs]

end PureDaggerKernel

/-- **224VI** (`exc-purec-no-biproduct`, eff.tex:7206, Exercise\*):
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

/-- **224VII** (`exc-purec-equal`, eff.tex:7235, Exercise\*):
`Pure (vNᵒᵖ)` does not have all coequalizers. -/
theorem exc_purec_equal (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasCoequalizers (PureCat WStarCPSU.{u}ᵒᵖ) := sorry

/-! ## Sequential effect algebras (parsec 225) -/

/-- **225IV** (eff.tex:7369, Definition): a **sequential effect algebra**
(SEA) is an effect algebra with a binary operation `&` satisfying

* (S1) `c & (–)` is additive;
* (S2) `1 & a = a`;
* (S3) `a & b = 0` implies `b & a = 0`;
* (S4) if `a & b = b & a` then `a & bᵖ = bᵖ & a` and
  `(a & b) & c = a & (b & c)`;
* (S5) if `c` commutes (w.r.t. `&`) with `a` and with `b`, and `a ⊥ b`,
  then `c` commutes with `a & b` and with `a ⋁ b`. -/
class SequentialEffectAlgebra (E : Type u) [EffectAlgebra E] where
  seq : E → E → E
  seq_add : ∀ (c : E) {a b : E} (h : Perp a b),
    ∃ h' : Perp (seq c a) (seq c b),
      ovee (seq c a) (seq c b) h' = seq c (ovee a b h)
  one_seq : ∀ a : E, seq 1 a = a
  seq_zero_comm : ∀ a b : E, seq a b = 0 → seq b a = 0
  seq_comm_orth : ∀ {a b : E}, seq a b = seq b a → seq a (orth b) = seq (orth b) a
  seq_comm_assoc : ∀ {a b : E}, seq a b = seq b a →
    ∀ c : E, seq (seq a b) c = seq a (seq b c)
  seq_comm_compat : ∀ {a b c : E} (h : Perp a b),
    seq c a = seq a c → seq c b = seq b c →
      seq c (seq a b) = seq (seq a b) c ∧
      seq c (ovee a b h) = seq (ovee a b h) c

/-- **225V** (eff.tex:7398, Examples): the effect algebra `[0,1]_𝒜` of a
von Neumann algebra is a sequential effect algebra with
`a & b = √a b √a`. -/
theorem effects_sea (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (SequentialEffectAlgebra (Theses.effects A)) := sorry

/-- **225V** (eff.tex:7398, Examples): any commutative effect monoid is a
sequential effect algebra with `a & b = a ⊙ b`. -/
theorem commutative_effectMonoid_sea (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) :
    Nonempty (SequentialEffectAlgebra M) :=
  ⟨{ seq := fun a b => a * b
     seq_add := fun c _ _ h =>
       let ⟨h', e⟩ := emon_mul_ovee c h
       ⟨h', e.symm⟩
     one_seq := EffectMonoid.one_mul
     seq_zero_comm := fun a b hab => (hc b a).trans hab
     seq_comm_orth := fun {a b} _ => hc a (orth b)
     seq_comm_assoc := fun {a b} _ c => EffectMonoid.mul_assoc a b c
     seq_comm_compat := fun {a b c} h _ _ => ⟨hc c (a * b), hc c (ovee a b h)⟩ }⟩

/-- **225VI** (eff.tex:7405, Proposition): in a †-effectus, the predicates
`Pred X` with `p & q = q ∘ asrt_p` satisfy axioms (S1), (S2) and (S3) of a
sequential effect algebra.  (Whether they form a SEA is open, 225VIII.) -/
theorem pred_sea_s1_s2_s3 [AndThenEffectus C] [DaggerPrimeEffectus C]
    (X : C) :
    (∀ (c : Pred X) {p q : Pred X} (h : Perp p q),
      ∃ h' : Perp (andThen c p) (andThen c q),
        ovee (andThen c p) (andThen c q) h' = andThen c (ovee p q h)) ∧
    (∀ p : Pred X, andThen 1 p = p) ∧
    (∀ p q : Pred X, andThen p q = 0 → andThen q p = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (S1): `c & (–)` is additive, because precomposition with `asrt c`
    -- preserves partial sums (`FinPAC.ovee_comp`).
    intro c p q h
    obtain ⟨h', e⟩ := FinPAC.ovee_comp h (asrt c)
    exact ⟨h', e.symm⟩
  · -- (S2): `asrt_1 = id`, by the absorption rule 211XV for the sharp
    -- predicate `1` (`1 ∘ p ≤ 1` always holds).
    intro p
    exact ((asrt_absorp_rule p (isSharp_one (effObj C)) (isSharp_one X)).2).mp
      (pred_le_truth _)
  · -- (S3): the thesis (eff.tex:7415) applies the dagger to
    -- `asrt_q ∘ asrt_p = 0 = asrt_0`.  We avoid `pureDagger`
    -- and argue instead with the `asrt_sq` axiom of a †-effectus together
    -- with the uniqueness of square roots; see the errata note.
    intro p q h
    -- `asrt p ≫ asrt q = 0`, since `1 ∘ asrt_q = q`.
    have hpq : asrt p ≫ asrt q = (0 : X ⟶ X) := by
      refine EffectusPartialForm.eq_zero_of_one_zero ?_
      show (asrt p ≫ asrt q) ≫ truth X = 0
      rw [Category.assoc, (asrt_spec q).2]
      exact h
    -- Hence `asrt_{q&p} ∘ asrt_{q&p} = asrt_q ∘ asrt_p ∘ asrt_p ∘ asrt_q = 0`.
    have hsq : asrt (andThen q p) ≫ asrt (andThen q p) = (0 : X ⟶ X) := by
      rw [DaggerPrimeEffectus.asrt_sq q p, hpq, FinPAC.comp_zero,
        FinPAC.comp_zero]
    -- So `(q&p) & (q&p) = 0 = 0 & 0`, and square roots of `0` are unique.
    have hr : andThen (andThen q p) (andThen q p) = (0 : Pred X) := by
      have e : andThen (andThen q p) (andThen q p)
          = (asrt (andThen q p) ≫ asrt (andThen q p)) ≫ truth X := by
        show asrt (andThen q p) ≫ andThen q p = _
        rw [Category.assoc, (asrt_spec (andThen q p)).2]
      rw [e, hsq, FinPAC.zero_comp]
    have hz : andThen (0 : Pred X) 0 = (0 : Pred X) := FinPAC.comp_zero _
    exact (DaggerPrimeEffectus.sqrt_existsUnique (0 : Pred X)).unique hr hz

/-! ## Homological categories (parsecs 226–228) -/

section Homological

variable [AndThenEffectus C]

/-- **226II** (`homology-lemma`, eff.tex:7440, Lemma): for sharp predicates
`s, t` on the same object of a †-effectus with `sᵖ ≤ t`, the predicate
`s & t` is sharp. -/
theorem homology_lemma [DaggerPrimeEffectus C] {X : C} {s t : Pred X}
    (hs : IsSharp s) (ht : IsSharp t) (h : orth s ≼ t) :
    IsSharp (andThen s t) := by
  -- `sᵖ ≤ t` is `tᵖ ≤ s`, so `s & tᵖ = tᵖ` by the absorption rule 213V
  have hts : orth t ≼ s := by
    have h' := eabasics_le_iff_orth_le.mp h
    rwa [eabasics_orth_orth] at h'
  have habs : asrt s ≫ orth t = orth t := (simple_andthen_absorption hs).mp hts
  -- (S1): `(s & t) ⋁ (s & tᵖ) = s & 1 = s`, so `s & t ⊥ tᵖ`, i.e. `s & t ≤ t`
  obtain ⟨hperp, -⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth t) (asrt s)
  rw [habs] at hperp
  have hle_t : andThen s t ≼ t := by
    have h' := eabasics_perp_iff_le_orth.mp hperp
    rwa [eabasics_orth_orth] at h'
  -- `s & t ≤ s & 1 = s`
  have hle_s : andThen s t ≼ s := by
    have h' := comp_le_comp (asrt s) (pred_le_truth t)
    rwa [(asrt_spec s).2] at h'
  -- the infimum `m = s ∧ t` in `SPred X` (208IX)
  obtain ⟨m, hms, hmt, hmax⟩ :
      ∃ m : SPred X, m.1 ≼ s ∧ m.1 ≼ t ∧
        ∀ r : SPred X, r.1 ≼ s → r.1 ≼ t → r.1 ≼ m.1 :=
    ⟨_, spred_infimum ⟨s, hs⟩ ⟨t, ht⟩⟩
  -- `⌈s & t⌉` is a sharp lower bound of `s` and `t`, hence below `m`
  have hcm : ceilPred (andThen s t) ≼ m.1 := by
    refine hmax ⟨ceilPred (andThen s t), isSharp_ceil _⟩ ?_ ?_
    · have h' := ceil_mono hle_s; rwa [ceil_of_isSharp hs] at h'
    · have h' := ceil_mono hle_t; rwa [ceil_of_isSharp ht] at h'
  -- conversely `m = s & m ≤ s & t`, again by 213V
  have hmst : m.1 ≼ andThen s t := by
    have h' := comp_le_comp (asrt s) hmt
    rwa [show asrt s ≫ m.1 = m.1 from (simple_andthen_absorption hs).mp hms] at h'
  -- so `⌈s & t⌉ ≤ m ≤ s & t ≤ ⌈s & t⌉`
  have hfix : ceilPred (andThen s t) = andThen s t :=
    eabasics_le_antisymm (pcm_preorder_trans hcm hmst) (le_ceil _)
  rw [← hfix]
  exact isSharp_ceil _

/-- **226IV.1** (eff.tex:7483, Definition): the preorder on kernels:
`n ≤ m` when `n` factors through `m` (Grandis; `n ≈ m` when both `n ≤ m`
and `m ≤ n`, and `Nsb A` is the poset of kernels modulo `≈` — the latter
is represented in a ⋄-effectus by `SPred A`, cf. 227III). -/
def KernelLE {W W' X : C} (n : W ⟶ X) (m : W' ⟶ X) : Prop :=
  ∃ f : W ⟶ W', f ≫ m = n

/-- **226IV.2** (eff.tex:7483, Definition): a map `f` is **exact** when the
unique `g` with `f = ker (cok f) ∘ g ∘ cok (ker f)` is an isomorphism.
(An effectus with comprehension, quotients and images is *pointed
semiexact*: it has a zero object and all kernels and cokernels, by 200III
and 205II.) -/
def IsExactMap {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (W Q K Q' : C) (kf : W ⟶ X) (ckf : X ⟶ Q) (cf : Y ⟶ Q') (kcf : K ⟶ Y)
    (g : Q ⟶ K),
    IsKernel f kf ∧ IsCokernel kf ckf ∧ IsCokernel f cf ∧ IsKernel cf kcf ∧
      IsIso g ∧ f = ckf ≫ g ≫ kcf

/-- Kernels are unique up to isomorphism (the standard argument, needed for
226V.1). -/
theorem isKernel_unique {W W' X Y : C} {g : X ⟶ Y} {k : W ⟶ X} {k' : W' ⟶ X}
    (h : IsKernel g k) (h' : IsKernel g k') :
    ∃ θ : W ⟶ W', IsIso θ ∧ θ ≫ k' = k := by
  obtain ⟨θ, hθ, -⟩ := h'.2 k h.1
  obtain ⟨θ', hθ', -⟩ := h.2 k' h'.1
  refine ⟨θ, ⟨⟨θ', ?_, ?_⟩⟩, hθ⟩
  · obtain ⟨u, -, huu⟩ := h.2 k h.1
    rw [huu (θ ≫ θ') (by show (θ ≫ θ') ≫ k = k; rw [Category.assoc, hθ', hθ]),
      huu (𝟙 W) (Category.id_comp _)]
  · obtain ⟨u, -, huu⟩ := h'.2 k' h'.1
    rw [huu (θ' ≫ θ) (by show (θ' ≫ θ) ≫ k' = k'; rw [Category.assoc, hθ, hθ']),
      huu (𝟙 W') (Category.id_comp _)]

/-- Cokernels are unique up to isomorphism (needed for 226V.2). -/
theorem isCokernel_unique {X Y Q Q' : C} {g : X ⟶ Y} {c : Y ⟶ Q} {c' : Y ⟶ Q'}
    (h : IsCokernel g c) (h' : IsCokernel g c') :
    ∃ θ : Q ⟶ Q', IsIso θ ∧ c ≫ θ = c' := by
  obtain ⟨θ, hθ, -⟩ := h.2 c' h'.1
  obtain ⟨θ', hθ', -⟩ := h'.2 c h.1
  refine ⟨θ, ⟨⟨θ', ?_, ?_⟩⟩, hθ⟩
  · obtain ⟨u, -, huu⟩ := h.2 c h.1
    rw [huu (θ ≫ θ') (by show c ≫ θ ≫ θ' = c; rw [← Category.assoc, hθ, hθ']),
      huu (𝟙 Q) (Category.comp_id _)]
  · obtain ⟨u, -, huu⟩ := h'.2 c' h'.1
    rw [huu (θ' ≫ θ) (by show c' ≫ θ' ≫ θ = c'; rw [← Category.assoc, hθ', hθ]),
      huu (𝟙 Q') (Category.comp_id _)]

/-- **226V.1** (eff.tex:7523, Theorem): in a †-effectus (in partial form)
a map is a kernel iff it is a comprehension. -/
theorem homological_kernels [DaggerPrimeEffectus C] {W X : C} (f : W ⟶ X) :
    (∃ (Y : C) (g : X ⟶ Y), IsKernel g f) ↔
      ∃ p : Pred X, IsComprehension p f := by
  constructor
  · -- a kernel of `g` is isomorphic to the comprehension for `(1∘g)ᵖ` (200III)
    rintro ⟨Y, g, hk⟩
    obtain ⟨θ, hθ, hcomm⟩ :=
      isKernel_unique hk (effectus_kernels g (isComprehension_comprMap _))
    haveI := hθ
    refine ⟨orth (g ≫ truth Y), ?_⟩
    rw [← hcomm]
    exact compr_basics_1 (isComprehension_comprMap _) θ
  · -- a comprehension for `p` is a kernel of `pᵖ` (200V)
    rintro ⟨p, hp⟩
    exact ⟨effObj C, orth p, (compr_is_kernel p f).mp hp⟩

/-- **226V.2** (eff.tex:7523, Theorem): a map is a cokernel iff it is a
quotient for a sharp predicate. -/
theorem homological_cokernels [DaggerPrimeEffectus C] {X Y : C}
    (f : X ⟶ Y) :
    (∃ (Z : C) (g : Z ⟶ X), IsCokernel g f) ↔
      ∃ s : Pred X, IsSharp s ∧ IsQuotient s f := by
  constructor
  · -- a cokernel of `g` is isomorphic to the quotient for `im g` (205II)
    rintro ⟨Z, g, hc⟩
    obtain ⟨θ, hθ, hcomm⟩ :=
      isCokernel_unique (effectus_cokernels g (isQuotient_quotMap _)) hc
    haveI := hθ
    refine ⟨imPred g, isSharp_imPred C g, ?_⟩
    rw [← hcomm]
    exact quotient_basics_1 (isQuotient_quotMap _) θ
  · -- a quotient for a sharp `s` is a cokernel of `π_s` (205IV)
    rintro ⟨s, hs, hq⟩
    exact ⟨comprObj s, comprMap s, (exc_cokernels hs f).mp hq⟩

/-- **226V.3** (eff.tex:7523, Theorem): a map is exact iff it is
pristine. -/
theorem homological_exact [DaggerPrimeEffectus C] {X Y : C} (f : X ⟶ Y) :
    IsExactMap f ↔ Pristine f := by
  constructor
  · -- `f = cok(ker f) ∘ g ∘ ker(cok f)` with `g` iso: the outer maps are a
    -- quotient for a sharp predicate and a comprehension (226V.1/2), so `f`
    -- is pure and `1 ∘ f = 1 ∘ cok(ker f) = sᵖ` is sharp.
    rintro ⟨W, Q, K, Q', kf, ckf, cf, kcf, g, hkf, hck, hcf, hkcf, hg, hform⟩
    haveI := hg
    obtain ⟨s, hs, hq⟩ := (homological_cokernels ckf).mp ⟨W, kf, hck⟩
    obtain ⟨p, hp⟩ := (homological_kernels kcf).mp ⟨Q', cf, hkcf⟩
    have htot : (g ≫ kcf) ≫ truth Y = truth Q := by
      rw [Category.assoc, compr_total hp]
      exact iso_isTotal g
    refine ⟨⟨Q, ckf, g ≫ kcf, s, p, hq, compr_basics_1 hp g, hform⟩, ?_⟩
    · have h1 : f ≫ truth Y = orth s := by
        rw [hform, Category.assoc, htot, quotient_basics_5 hq]
      rw [h1]
      exact DiamondEffectus.orth_sharp hs
  · -- conversely, a pristine `h` is `π_{im h} ∘ α ∘ ζ_{1∘h}` (218VI), and
    -- `ζ_{1∘h}` is a cokernel of `ker f = π_{(1∘f)ᵖ}` while `π_{im f}` is a
    -- kernel of `cok f = ξ_{im f}`.
    intro hpr
    obtain ⟨α, hform⟩ := standard_form_pristine hpr
    have hos : IsSharp (orth (f ≫ truth Y)) :=
      DiamondEffectus.orth_sharp hpr.2
    refine ⟨comprObj (orth (f ≫ truth Y)), comprObj (f ≫ truth Y),
      comprObj (imPred f), quotObj (imPred f),
      comprMap (orth (f ≫ truth Y)), zetaMap (f ≫ truth Y) hpr.2,
      quotMap (imPred f), comprMap (imPred f), α.hom,
      effectus_kernels f (isComprehension_comprMap _), ?_,
      effectus_cokernels f (isQuotient_quotMap _), ?_, inferInstance, hform⟩
    · -- `im π_{(1∘f)ᵖ} = (1∘f)ᵖ` and `ζ_{1∘f}` is a quotient for it
      refine effectus_cokernels _ ?_
      rw [(img_of_compr (orth (f ≫ truth Y))).2 _ hos]
      exact (zetaMap_spec (f ≫ truth Y) hpr.2).1
    · -- `1 ∘ ξ_{im f} = (im f)ᵖ`, so its kernel is a comprehension for `im f`
      refine effectus_kernels _ ?_
      rw [quotient_basics_5 (isQuotient_quotMap (imPred f)), eabasics_orth_orth]
      exact isComprehension_comprMap _

/-- **226V** (eff.tex:7523, Theorem): a †-effectus is a pointed
homological category: kernels and cokernels are closed under composition,
and (**226VII**, homology axiom) for a kernel `m` and cokernel `q` with
`ker q ≤ m`, the composite `q ∘ m` is exact. -/
theorem homological_category [DaggerPrimeEffectus C] :
    (∀ {W X Y Z : C} (m₁ : W ⟶ X) (m₂ : X ⟶ Y),
      (∃ g : X ⟶ Z, IsKernel g m₁) → (∃ (Z' : C) (g : Y ⟶ Z'), IsKernel g m₂) →
        ∃ (Z'' : C) (g : Y ⟶ Z''), IsKernel g (m₁ ≫ m₂)) ∧
    (∀ {X Y Z W' : C} (q₁ : X ⟶ Y) (q₂ : Y ⟶ Z),
      (∃ g : W' ⟶ X, IsCokernel g q₁) →
      (∃ (W'' : C) (g : W'' ⟶ Y), IsCokernel g q₂) →
        ∃ (W''' : C) (g : W''' ⟶ X), IsCokernel g (q₁ ≫ q₂)) ∧
    (∀ {M A Q : C} (m : M ⟶ A) (q : A ⟶ Q)
      (_ : ∃ (Y : C) (g : A ⟶ Y), IsKernel g m)
      (_ : ∃ (Z : C) (g : Z ⟶ A), IsCokernel g q)
      (_ : ∀ (K : C) (kq : K ⟶ A), IsKernel q kq → KernelLE kq m),
        IsExactMap (m ≫ q)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- kernels are comprehensions (226V.1), and comprehensions compose (211XI)
    intro W X Y Z m₁ m₂ h₁ h₂
    obtain ⟨g, hg⟩ := h₁
    obtain ⟨p, hp⟩ := (homological_kernels m₁).mp ⟨Z, g, hg⟩
    obtain ⟨q, hq⟩ := (homological_kernels m₂).mp h₂
    obtain ⟨r, hr⟩ := upm_closed_compr hp hq
    exact ⟨effObj C, orth r, (compr_is_kernel r (m₁ ≫ m₂)).mp hr⟩
  · -- cokernels are quotients for sharp predicates (226V.2), and quotients
    -- compose (197VII); the predicate `(ζ₁ ∘ s₂ᵖ)ᵖ` of the composite is
    -- sharp because `ζ₁` is a sharp map
    intro X Y Z W' q₁ q₂ h₁ h₂
    obtain ⟨g, hg⟩ := h₁
    obtain ⟨s₁, hs₁, hq₁⟩ := (homological_cokernels q₁).mp ⟨W', g, hg⟩
    obtain ⟨s₂, hs₂, hq₂⟩ := (homological_cokernels q₂).mp h₂
    have hq₁' : IsQuotient (orth (orth s₁)) q₁ := by rwa [eabasics_orth_orth]
    have hq₂' : IsQuotient (orth (orth s₂)) q₂ := by rwa [eabasics_orth_orth]
    have hsharp : IsSharp (orth (q₁ ≫ orth s₂)) :=
      DiamondEffectus.orth_sharp
        (DaggerPrimeEffectus.quot_sharp hs₁ hq₁ _ (DiamondEffectus.orth_sharp hs₂))
    exact ⟨_, comprMap _,
      (exc_cokernels hsharp (q₁ ≫ q₂)).mp (quotients_composition hq₁' hq₂')⟩
  · -- the homology axiom (226VII)
    intro M A Q m q hm hq hker
    obtain ⟨r, hmr⟩ := (homological_kernels m).mp hm
    obtain ⟨s₀, hs₀, hq₀⟩ := (homological_cokernels q).mp hq
    -- `1 ∘ q = s₀ᵖ` is sharp, and `m` is a comprehension for the sharp `im m`
    have hps : IsSharp (q ≫ truth Q) := by
      rw [quotient_basics_5 hq₀]; exact DiamondEffectus.orth_sharp hs₀
    have hmim : IsComprehension (imPred m) m := isComprehension_imPred hmr
    have hims : IsSharp (imPred m) := isSharp_imPred C m
    -- `ker q ≤ m` gives `im (ker q) = (1 ∘ q)ᵖ ≤ im m`, i.e. `imᵖ m ≤ 1 ∘ q`
    obtain ⟨f, hf⟩ := hker (comprObj (orth (q ≫ truth Q)))
      (comprMap (orth (q ≫ truth Q)))
      (effectus_kernels q (isComprehension_comprMap _))
    have hle : orth (imPred m) ≼ q ≫ truth Q := by
      have h1 : imPred (comprMap (orth (q ≫ truth Q))) ≼ imPred m := by
        rw [← hf]; exact (im_ineq m f).1
      rw [(img_of_compr (orth (q ≫ truth Q))).2 _
        (DiamondEffectus.orth_sharp hps)] at h1
      have h2 := eabasics_le_iff_orth_le.mp h1
      rwa [eabasics_orth_orth] at h2
    -- 226II: `(im m) & (1 ∘ q)` is sharp
    have hsharp := homology_lemma hims hps hle
    -- `ζ` for the comprehension `m` (211VII); it is a sharp map, and it is
    -- the map the thesis writes as `m†`
    obtain ⟨ζ, ⟨hζq, hmζ, hζm⟩, -⟩ := prop_corr_zeta_pi_compr hims hmim
    have hζsharp : SharpMap ζ :=
      DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp hims) hζq
    refine (homological_exact (m ≫ q)).mpr
      ⟨upm_closed_pure (isPure_comprehension C hmr) (isPure_of_isQuotient hq₀), ?_⟩
    have hw : ζ ≫ ((m ≫ q) ≫ truth Q) = andThen (imPred m) (q ≫ truth Q) := by
      show ζ ≫ ((m ≫ q) ≫ truth Q) = asrt (imPred m) ≫ (q ≫ truth Q)
      rw [← Category.assoc, ← Category.assoc, hζm, Category.assoc]
    have key : ceilPred ((m ≫ q) ≫ truth Q) = (m ≫ q) ≫ truth Q := by
      calc ceilPred ((m ≫ q) ≫ truth Q)
          = (m ≫ ζ) ≫ ceilPred ((m ≫ q) ≫ truth Q) := by
            rw [hmζ, Category.id_comp]
        _ = m ≫ ceilPred (ζ ≫ ((m ≫ q) ≫ truth Q)) := by
            rw [Category.assoc, (sharp_ceil ζ).mp hζsharp]
        _ = (m ≫ ζ) ≫ ((m ≫ q) ≫ truth Q) := by
            rw [hw, ceil_of_isSharp hsharp, ← hw]
            simp only [Category.assoc]
        _ = (m ≫ q) ≫ truth Q := by rw [hmζ, Category.id_comp]
    rw [← key]
    exact isSharp_ceil _

/-- **227II.1** (eff.tex:7586, Definition): a composable pair
`A → f → B → g → C` is **exact at** `B` when `ker (cok f) ≈ ker g`.  (In a
†-effectus this amounts to `imᵖ f = ⌈1 ∘ g⌉`, 227III.1.) -/
def ExactAt {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∃ (Q K K' : C) (cf : Y ⟶ Q) (k : K ⟶ Y) (k' : K' ⟶ Y),
    IsCokernel f cf ∧ IsKernel cf k ∧ IsKernel g k' ∧
      KernelLE k k' ∧ KernelLE k' k

/-- **227III.1** (eff.tex:7622, Example): in a †-effectus, `f ∘ g` is
exact at the middle object iff `imᵖ f = ⌈1 ∘ g⌉`. -/
theorem exactAt_iff [DaggerPrimeEffectus C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    ExactAt f g ↔ orth (imPred f) = ceilPred (g ≫ truth Z) := by
  -- `⌊(1∘g)ᵖ⌋ = ⌈1∘g⌉ᵖ`, so the standard kernel of `g` has image `⌈1∘g⌉ᵖ`
  have hfloor : floorPred (orth (g ≫ truth Z)) = orth (ceilPred (g ≫ truth Z)) := by
    show _ = orth (orth (floorPred (orth (g ≫ truth Z))))
    rw [eabasics_orth_orth]
  constructor
  · rintro ⟨Q, K, K', cf, k, k', hcf, hk, hk', ⟨u, hu⟩, ⟨v, hv⟩⟩
    -- a cokernel of `f` is a quotient for `im f`, so `1 ∘ cf = (im f)ᵖ`
    obtain ⟨θ, hθ, hcomm⟩ :=
      isCokernel_unique (effectus_cokernels f (isQuotient_quotMap (imPred f))) hcf
    haveI := hθ
    have hcfq : IsQuotient (imPred f) cf := by
      rw [← hcomm]; exact quotient_basics_1 (isQuotient_quotMap _) θ
    have hcft : cf ≫ truth Q = orth (imPred f) := quotient_basics_5 hcfq
    -- and a kernel of `cf` is a comprehension for `(1∘cf)ᵖ = im f`
    obtain ⟨θ₁, hθ₁, hcomm₁⟩ :=
      isKernel_unique hk (effectus_kernels cf (isComprehension_comprMap _))
    haveI := hθ₁
    have himk : imPred k = imPred f := by
      rw [← hcomm₁,
        (im_ineq (comprMap (orth (cf ≫ truth Q))) θ₁).2 θ₁ inferInstance]
      show floorPred (orth (cf ≫ truth Q)) = _
      rw [hcft, eabasics_orth_orth]
      exact (img_of_compr (imPred f)).1.mp (isSharp_imPred C f)
    obtain ⟨θ₂, hθ₂, hcomm₂⟩ :=
      isKernel_unique hk' (effectus_kernels g (isComprehension_comprMap _))
    haveI := hθ₂
    have himk' : imPred k' = orth (ceilPred (g ≫ truth Z)) := by
      rw [← hcomm₂,
        (im_ineq (comprMap (orth (g ≫ truth Z))) θ₂).2 θ₂ inferInstance]
      exact hfloor
    -- `k ≈ k'` gives `im k = im k'`
    have h1 : imPred k ≼ imPred k' := by
      have h := (im_ineq k' u).1
      rwa [hu] at h
    have h2 : imPred k' ≼ imPred k := by
      have h := (im_ineq k v).1
      rwa [hv] at h
    have hkey : imPred f = orth (ceilPred (g ≫ truth Z)) := by
      rw [← himk, ← himk']
      exact eabasics_le_antisymm h1 h2
    rw [hkey, eabasics_orth_orth]
  · intro h
    -- conversely, take the standard cokernel and kernels
    refine ⟨quotObj (imPred f), comprObj (orth (quotMap (imPred f) ≫
        truth (quotObj (imPred f)))), comprObj (orth (g ≫ truth Z)),
      quotMap (imPred f), comprMap _, comprMap _,
      effectus_cokernels f (isQuotient_quotMap (imPred f)),
      effectus_kernels _ (isComprehension_comprMap _),
      effectus_kernels g (isComprehension_comprMap _), ?_, ?_⟩ <;>
    · -- both kernels are comprehensions for `im f`, hence isomorphic
      have him : imPred (comprMap (orth (quotMap (imPred f) ≫
          truth (quotObj (imPred f))))) = imPred f := by
        show floorPred _ = _
        rw [quotient_basics_5 (isQuotient_quotMap (imPred f)),
          eabasics_orth_orth]
        exact (img_of_compr (imPred f)).1.mp (isSharp_imPred C f)
      have him' : imPred (comprMap (orth (g ≫ truth Z))) = imPred f := by
        show floorPred (orth (g ≫ truth Z)) = _
        rw [hfloor, ← h, eabasics_orth_orth]
      obtain ⟨θ, hθ, hcomm, -⟩ :=
        compr_basics_2 (him ▸ isComprehension_imPred (isComprehension_comprMap _))
          (him' ▸ isComprehension_imPred (isComprehension_comprMap _))
      haveI := hθ
      first
        | exact ⟨θ, hcomm⟩
        | exact ⟨inv θ, by rw [← hcomm, ← Category.assoc, IsIso.inv_hom_id,
            Category.id_comp]⟩

/-- Helper for 227V: the thesis's computation `π^□(π_⋄(s)) =
⌈(s ∘ π†)ᵖ ∘ π⌉ᵖ = ⌈(s ∘ π† ∘ π)ᵖ⌉ᵖ = s`, isolated from the particular
`π`: it needs only that `π` is total, that its "dagger" `g` is a sharp map
with `π ∘ g = id` (in diagrammatic order `π ≫ g = 𝟙`), and that
`π_⋄ = g^⋄`. -/
theorem boxPull_diaPush_of_sharp_section {W X : C} {f : W ⟶ X} {g : X ⟶ W}
    (htot : IsTotal f) (hg : SharpMap g) (hfg : f ≫ g = 𝟙 W)
    (hadj : diaPush f = diaPull g) (s : SPred W) :
    boxPull f (diaPush f s) = s := by
  have h1 : (diaPush f s).1 = g ≫ s.1 := by
    rw [hadj]; exact ceil_of_isSharp (hg s.1 s.2)
  apply Subtype.ext
  show orth (ceilPred (f ≫ orth (diaPush f s).1)) = s.1
  rw [h1, total_comp_orth htot, ← Category.assoc, hfg, Category.id_comp,
    ceil_of_isSharp (DiamondEffectus.orth_sharp s.2), eabasics_orth_orth]

/-- Helper for 227V, the dual of `boxPull_diaPush_of_sharp_section`: the
thesis's `ζ_⋄(ζ^□(s)) = ⌈(⌈sᵖ⌉ ∘ ζ ∘ ζ†)ᵖ⌉ = s`. -/
theorem diaPush_boxPull_of_sharp_retract {X W : C} {f : X ⟶ W} {g : W ⟶ X}
    (htot : IsTotal g) (hf : SharpMap f) (hgf : g ≫ f = 𝟙 W)
    (hadj : diaPush f = diaPull g) (t : SPred W) :
    diaPush f (boxPull f t) = t := by
  have h1 : (boxPull f t).1 = orth (f ≫ orth t.1) := by
    show orth (ceilPred (f ≫ orth t.1)) = _
    rw [ceil_of_isSharp (hf _ (DiamondEffectus.orth_sharp t.2))]
  apply Subtype.ext
  rw [hadj]
  show ceilPred (g ≫ (boxPull f t).1) = t.1
  rw [h1, total_comp_orth htot, ← Category.assoc, hgf, Category.id_comp,
    eabasics_orth_orth, ceil_of_isSharp t.2]

/-- **227V** (`diamondboxlemma`, eff.tex:7653, Lemma), first half: in a
†-effectus, `π^□ ∘ π_⋄ = id` for any comprehension `π`. -/
theorem diamondboxlemma_compr [DaggerPrimeEffectus C] {W X : C}
    {p : Pred X} {π : W ⟶ X} (hπ : IsComprehension p π) (s : SPred W) :
    boxPull π (diaPush π s) = s := by
  -- `π = β ∘ π_{⌊p⌋}` for an iso `β`, and `π†` is `β⁻¹ ∘ ζ_{⌊p⌋}`
  obtain ⟨θ, hθiso, hθ, -⟩ := compr_basics_2 hπ (isComprehension_comprMap p)
  obtain ⟨α, hαiso, hα⟩ := floor_basics_2 p
  haveI := hθiso
  haveI := hαiso
  haveI : IsIso (θ ≫ α) := inferInstance
  have hfs : IsSharp (floorPred p) := isSharp_floor p
  obtain ⟨hq', hπζ', -⟩ := zetaMap_spec (floorPred p) hfs
  have hπeq : π = (θ ≫ α) ≫ comprMap (floorPred p) := by
    rw [Category.assoc, hα, hθ]
  refine boxPull_diaPush_of_sharp_section (g := zetaMap (floorPred p) hfs ≫
      inv (θ ≫ α)) (compr_total hπ) ?_ ?_ ?_ s
  · intro q hq
    rw [Category.assoc]
    exact DaggerPrimeEffectus.quot_sharp (DiamondEffectus.orth_sharp hfs) hq'
      _ (iso_diamond_adjoint_1 (inv (θ ≫ α)) hq)
  · rw [hπeq]
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap (floorPred p)), hπζ', Category.id_comp,
      ← Category.assoc, IsIso.hom_inv_id]
  · funext u
    rw [hπeq, diaPush_comp, diaPull_comp,
      (exc_diamond_adj_1 (comprMap (floorPred p)) (zetaMap (floorPred p) hfs)).mp
        (quotcompr_diamond_adjoint hfs),
      (exc_diamond_adj_1 (θ ≫ α) (inv (θ ≫ α))).mp
        (iso_diamond_adjoint_2 (θ ≫ α)).2.2]

/-- **227V** (`diamondboxlemma`, eff.tex:7653, Lemma), second half:
`ζ_⋄ ∘ ζ^□ = id` for any sharp quotient `ζ`. -/
theorem diamondboxlemma_quot [DaggerPrimeEffectus C] {X W : C}
    {s₀ : Pred X} (hs : IsSharp s₀) {ζ : X ⟶ W}
    (hζ : IsQuotient s₀ ζ) (t : SPred W) :
    diaPush ζ (boxPull ζ t) = t := by
  -- `ζ = ζ_{s₀ᵖ} ∘ β` for an iso `β`, and `ζ†` is `π_{s₀ᵖ} ∘ β⁻¹`
  have hs' : IsSharp (orth s₀) := DiamondEffectus.orth_sharp hs
  obtain ⟨hq', hπζ', -⟩ := zetaMap_spec (orth s₀) hs'
  have hq'' : IsQuotient s₀ (zetaMap (orth s₀) hs') := by
    rwa [eabasics_orth_orth] at hq'
  obtain ⟨β, hβiso, hβ, -⟩ := quotient_basics_2 hζ hq''
  haveI := hβiso
  refine diaPush_boxPull_of_sharp_retract (g := inv β ≫ comprMap (orth s₀))
    (isTotal_comp (iso_isTotal (inv β))
      (compr_total (isComprehension_comprMap (orth s₀))))
    (DaggerPrimeEffectus.quot_sharp hs hζ) ?_ ?_ t
  · rw [← hβ]
    simp only [Category.assoc]
    rw [← Category.assoc (comprMap (orth s₀)), hπζ', Category.id_comp,
      IsIso.inv_hom_id]
  · funext u
    rw [← hβ, diaPush_comp, diaPull_comp,
      ← (quotcompr_diamond_adjoint hs' (X := X)),
      (exc_diamond_adj_1 β (inv β)).mp (iso_diamond_adjoint_2 β).2.2]

end Homological

section Snake

variable [AndThenEffectus C] [DaggerPrimeEffectus C]

/-- **228II** (eff.tex:7687, Snake Lemma; Grandis): suppose the diagram

```
        A --f--> B --g--> C --> 0
        |a       |b       |c
        v        v        v
  0 --> A'--h--> B'--k--> C'
```

commutes in a †-effectus with exact rows and the modularity conditions
(1)–(8) below (stated, following 227III, in terms of `(–)_⋄` and `(–)^□`
on sharp predicates):

1. `b^□(b_⋄(im f)) = ⌈1∘b⌉ᵖ ∨ im f`;
2. `b_⋄(b^□(im h)) = im h ∧ im b`;
3. `k^□(k_⋄(im b)) = im h ∨ im b`;
4. `f_⋄(f^□(b^□(0))) = ⌈1∘b⌉ᵖ ∧ im f`;
5. `imᵖ f = ⌈1∘g⌉` (exactness at `B`);
6. `imᵖ h = ⌈1∘k⌉` (exactness at `B'`);
7. `g` is a quotient for a sharp predicate; and
8. `h` is a comprehension.

Then, writing `a_π = π_{(1∘a)ᵖ}`, `a_ζ = ξ_{im a}` (and likewise for `b`,
`c`) for the chosen kernels and cokernels and

* `f̄ = b_π† ∘ f ∘ a_π`, `ḡ = c_π† ∘ g ∘ b_π`,
* `h̄ = b_ζ ∘ h ∘ a_ζ†`, `k̄ = c_ζ ∘ k ∘ b_ζ†`,

there is a connecting map `d : ker c ⟶ cok a` making

`ker a → ker b → ker c → cok a → cok b → cok c`

a long exact sequence. -/
theorem snake_lemma {A B C₃ A' B' C₃' : C}
    (f : A ⟶ B) (g : B ⟶ C₃) (a : A ⟶ A') (b : B ⟶ B') (c : C₃ ⟶ C₃')
    (h : A' ⟶ B') (k : B' ⟶ C₃')
    (w₁ : f ≫ b = a ≫ h) (w₂ : g ≫ c = b ≫ k)
    -- exact rows (conditions 5 and 6):
    (row₁ : ExactAt f g) (row₂ : ExactAt h k)
    -- conditions 7 and 8:
    (hg : ∃ s : Pred B, IsSharp s ∧ IsQuotient s g)
    (hh : ∃ p : Pred B', IsComprehension p h)
    -- modularity conditions (1)–(4):
    (m₁ : SPred.IsSup
      (SPred.orth ⟨ceilPred (b ≫ truth B'), isSharp_ceil _⟩)
      ⟨imPred f, isSharp_imPred C f⟩
      (boxPull b (diaPush b ⟨imPred f, isSharp_imPred C f⟩)))
    (m₂ : SPred.IsInf ⟨imPred h, isSharp_imPred C h⟩
      ⟨imPred b, isSharp_imPred C b⟩
      (diaPush b (boxPull b ⟨imPred h, isSharp_imPred C h⟩)))
    (m₃ : SPred.IsSup ⟨imPred h, isSharp_imPred C h⟩
      ⟨imPred b, isSharp_imPred C b⟩
      (boxPull k (diaPush k ⟨imPred b, isSharp_imPred C b⟩)))
    (m₄ : SPred.IsInf
      (SPred.orth ⟨ceilPred (b ≫ truth B'), isSharp_ceil _⟩)
      ⟨imPred f, isSharp_imPred C f⟩
      (diaPush f (boxPull f (boxPull b ⟨0, dia_isSharp_zero _⟩)))) :
    ∃ d : comprObj (orth (c ≫ truth C₃')) ⟶ quotObj (imPred a),
      -- the connecting sequence, with the induced maps on (co)kernels:
      letI fbar := comprMap (orth (a ≫ truth A')) ≫ f ≫
        pureDagger (comprMap (orth (b ≫ truth B')))
          (isPure_comprehension C (isComprehension_comprMap _))
      letI gbar := comprMap (orth (b ≫ truth B')) ≫ g ≫
        pureDagger (comprMap (orth (c ≫ truth C₃')))
          (isPure_comprehension C (isComprehension_comprMap _))
      letI hbar := pureDagger (quotMap (imPred a))
          (isPure_of_isQuotient (isQuotient_quotMap _)) ≫ h ≫
        quotMap (imPred b)
      letI kbar := pureDagger (quotMap (imPred b))
          (isPure_of_isQuotient (isQuotient_quotMap _)) ≫ k ≫
        quotMap (imPred c)
      ExactAt fbar gbar ∧ ExactAt gbar d ∧ ExactAt d hbar ∧
        ExactAt hbar kbar := sorry

end Snake

end Theses.B.Eff
