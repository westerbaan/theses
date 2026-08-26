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

/-- **224II** (eff.tex:7121, Definition): in a †-category, `f` is
**†-mono** when `f† ∘ f = id`. -/
def DaggerCat.DagMono {X Y : D} (f : X ⟶ Y) : Prop :=
  f ≫ DaggerCat.dag f = 𝟙 X

/-- **224II** (eff.tex:7121, Definition): dually, `f` is **†-epi** when
`f ∘ f† = id`. -/
def DaggerCat.DagEpi {X Y : D} (f : X ⟶ Y) : Prop :=
  DaggerCat.dag f ≫ f = 𝟙 Y

/-- **224II** (eff.tex:7130, Definition): `f` is a **†-partial isometry**
when `f = m ∘ e` for a †-mono `m` and †-epi `e`. -/
def DaggerCat.DagPartialIsometry {X Y : D} (f : X ⟶ Y) : Prop :=
  ∃ (Z : D) (e : X ⟶ Z) (m : Z ⟶ Y),
    DaggerCat.DagEpi e ∧ DaggerCat.DagMono m ∧ f = e ≫ m

/-- **224II** (eff.tex:7136, Definition): a **†-kernel** of `f` is an
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

/-- Helper for 224III (the first computation of eff.tex:7152): in a
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

/-- **224III.1** (eff.tex:7145, Proposition): in `Pure C` for a †-effectus
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

/-- **224III.1** (eff.tex:7145, Proposition), dually: a map of `Pure C` is
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

/-- **224III.2** (eff.tex:7145, Proposition): the †-partial isometries of
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

/-- **224III** (eff.tex:7156, Proposition): `Pure C` is a †-kernel
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

-- **224VI** (`exc-purec-no-biproduct`, eff.tex:7189, Exercise\*) and
-- **224VII** (`exc-purec-equal`, eff.tex:7218, Exercise\*),
-- `exc_purec_no_biproduct` and `exc_purec_equal`: `Pure (vNᵒᵖ)` has neither
-- binary coproducts nor all coequalizers.  Moved to
-- `Theses/B/Eff/VNExamples.lean` (author ruling 2026-08-17): they need
-- thesis A's von Neumann theory, and this file must keep importing only
-- `Theses.Common`.

/-! ## Sequential effect algebras (parsec 225) -/

/-- **225IV** (eff.tex:7352, Definition): a **sequential effect algebra**
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

-- **225V** (eff.tex:7381, Examples), `effects_sea`: the effect algebra
-- `[0,1]_𝒜` of a von Neumann algebra is a sequential effect algebra with
-- `a & b = √a b √a`.  Moved to `Theses/B/Eff/VNExamples.lean` (author
-- ruling 2026-08-17): it needs thesis A's von Neumann theory, and this file
-- must keep importing only `Theses.Common`.

/-- **225V** (eff.tex:7381, Examples), the structure: a commutative effect
monoid `M`, with the sequential product `a & b = a ⊙ b` the point names.
(S1) is `emon_mul_ovee`, (S2) is `EffectMonoid.one_mul`, and (S3)–(S5) are
all instances of commutativity, `a ⊙ b = b ⊙ a`, together with the
associativity of `⊙`. -/
def commEffectMonoidSEA (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) : SequentialEffectAlgebra M where
  seq a b := a * b
  seq_add := fun c _ _ h =>
    let ⟨h', e⟩ := emon_mul_ovee c h
    ⟨h', e.symm⟩
  one_seq := EffectMonoid.one_mul
  seq_zero_comm := fun a b hab => (hc b a).trans hab
  seq_comm_orth := fun {a b} _ => hc a (orth b)
  seq_comm_assoc := fun {a b} _ c => EffectMonoid.mul_assoc a b c
  seq_comm_compat := fun {a b c} h _ _ => ⟨hc c (a * b), hc c (ovee a b h)⟩

/-- **225V** (eff.tex:7381, Examples): any commutative effect monoid is a
sequential effect algebra with `a & b = a ⊙ b`.

The "with `a & b = a ⊙ b`" is **in the statement**: a bare
`Nonempty (SequentialEffectAlgebra M)` would assert only that *some*
sequential product exists on `M`, and the point names the one it means. -/
theorem commutative_effectMonoid_sea (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) :
    ∃ S : SequentialEffectAlgebra M, ∀ a b : M, S.seq a b = a * b :=
  ⟨commEffectMonoidSEA M hc, fun _ _ => rfl⟩

/-- **225VI** (eff.tex:7388, Proposition): in a †-effectus, the predicates
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
  · -- (S3): the thesis (eff.tex:7398) applies the dagger to
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

/-- Helper for 226II: the interior of the final part of the proof of 219XI
(`dagger-iso-mu`, eff.tex:6360–6398), extracted in the shape in which the
thesis's proof of `homology_lemma` (eff.tex:7434) invokes it — "by the same
reasoning as in the final part of the proof of `dagger-iso-mu` there exists a
(unique) pristine map `l` with …".  For predicates `a`, `b` on `X` there is a
pristine `l` with (in the thesis's order) `asrt_b ∘ asrt_a = l ∘ asrt_{a&b} =
asrt_{b&a} ∘ l`, `l† ∘ l = asrt_{⌈a&b⌉}` and `l ∘ l† = asrt_{⌈b&a⌉}`; below in
diagrammatic order.  `l` is the pristine part 218X of `asrt_a ∘ asrt_b`, which
is the `π_{⌈b&a⌉} ∘ ν⁻¹ ∘ ζ_{⌈a&b⌉}` of eff.tex:6360.  Kept `private`: it is
the interior of a thesis proof, not a statement of eff.tex. -/
private theorem exists_pristine_asrt_comp [DaggerPrimeEffectus C] {X : C}
    (a b : Pred X) :
    ∃ (l : X ⟶ X) (hl : IsPure l),
      asrt a ≫ asrt b = asrt (andThen a b) ≫ l ∧
      asrt a ≫ asrt b = l ≫ asrt (andThen b a) ∧
      l ≫ pureDagger l hl = asrt (ceilPred (andThen a b)) ∧
      pureDagger l hl ≫ l = asrt (ceilPred (andThen b a)) := by
  have hf : IsPure (asrt a ≫ asrt b) :=
    upm_closed_pure (asrt_spec a).1.1 (asrt_spec b).1.1
  have htruth : (asrt a ≫ asrt b) ≫ truth X = andThen a b := by
    rw [Category.assoc, (asrt_spec b).2]; rfl
  -- `(asrt_b ∘ asrt_a)† = asrt_a ∘ asrt_b` (219XV), so `im = ⌈b & a⌉` (209II.2)
  have hdagf : pureDagger (asrt a ≫ asrt b) hf = asrt b ≫ asrt a :=
    pureDagger_asrt_comp a b
  have him : imPred (asrt a ≫ asrt b) = ceilPred (andThen b a) := by
    have hadj : DiamondAdjoint (asrt a ≫ asrt b) (asrt b ≫ asrt a) := by
      have h := pureDagger_diamond_adjoint hf
      rwa [hdagf] at h
    have h := exc_diamond_adj_2 hadj
    rwa [Category.assoc, (asrt_spec a).2] at h
  -- 218X: `asrt_b ∘ asrt_a = l ∘ asrt_{a&b}` for a unique pristine `l` with
  -- `1 ∘ l = ⌈a&b⌉`, and `(asrt_b ∘ asrt_a)† = l† ∘ asrt_{a&b}`
  obtain ⟨l, ⟨hpris, h1, hd⟩, -⟩ := prist_asrt_decomp hf
  have himl : imPred l = ceilPred (andThen b a) :=
    (imPred_of_prist_asrt hpris h1 hd).trans him
  have hdd := prist_asrt_decomp_dagger hf hpris h1 hd
  rw [htruth] at h1 hd hdd
  rw [hdagf] at hdd
  -- `l ∘ l† = asrt_{1 ∘ l} = asrt_{⌈a&b⌉}` (218IX.3)
  have h3 : l ≫ pureDagger l hpris.1 = asrt (ceilPred (andThen a b)) := by
    rw [asrt_pristine_reverse_3 hpris, h1]
  -- `l†` is pristine too, with `1 ∘ l† = im l = ⌈b&a⌉`, so 218IX.3 at `l†`
  -- and `l†† = l` (218XII) give `l† ∘ l = asrt_{⌈b&a⌉}`
  have hprisd : Pristine (pureDagger l hpris.1) :=
    ⟨isPure_pureDagger hpris.1, by
      rw [pristine_dagger_truth hpris]; exact isSharp_imPred C l⟩
  have h4 : pureDagger l hpris.1 ≫ l = asrt (ceilPred (andThen b a)) := by
    have hid : pureDagger (pureDagger l hpris.1) hprisd.1 = l :=
      dagger_idempotent hpris.1
    have h := asrt_pristine_reverse_3 hprisd
    rw [hid, pristine_dagger_truth hpris, himl] at h
    exact h
  -- `l† ∘ (a&b) = b&a`, so 218IX.5 turns the decomposition around
  have hlab : pureDagger l hpris.1 ≫ andThen a b = andThen b a := by
    have h : (asrt b ≫ asrt a) ≫ truth X =
        (pureDagger l hpris.1 ≫ asrt (andThen a b)) ≫ truth X := by rw [hdd]
    simp only [Category.assoc] at h
    rw [(asrt_spec a).2, (asrt_spec (andThen a b)).2] at h
    exact h.symm
  have hB : l ≫ asrt (andThen b a) = asrt (andThen a b) ≫ l := by
    have h := asrt_pristine_reverse_5 hpris (p := andThen a b)
      (by rw [h1]; exact le_ceilPred _)
    rwa [hlab] at h
  exact ⟨l, hpris.1, hd, hd.trans hB.symm, h3, h4⟩

/-- **226II** (`homology-lemma`, eff.tex:7423, Lemma): for sharp predicates
`s, t` on the same object of a †-effectus with `sᵖ ≤ t`, the predicate
`s & t` is sharp. -/
theorem homology_lemma [DaggerPrimeEffectus C] {X : C} {s t : Pred X}
    (hs : IsSharp s) (ht : IsSharp t) (h : orth s ≼ t) :
    IsSharp (andThen s t) := by
  have hos : IsSharp (orth s) := DiamondEffectus.orth_sharp hs
  have hot : IsSharp (orth t) := DiamondEffectus.orth_sharp ht
  -- `sᵖ ⊥ tᵖ` (as `sᵖ ≤ t = tᵖᵖ`), so `tᵖ & sᵖ = 0` by 213III
  have hperp : Perp (orth s) (orth t) :=
    eabasics_perp_iff_le_orth.mpr (by rwa [eabasics_orth_orth])
  have hzero : asrt (orth t) ≫ orth s = (0 : Pred X) :=
    (perp_sharp_is_orth hos hot hperp).2
  -- hence `tᵖ & s = (tᵖ & s) ⋁ (tᵖ & sᵖ) = tᵖ & 1 = tᵖ`, which is sharp
  obtain ⟨hp0, e0⟩ :=
    FinPAC.ovee_comp (EffectAlgebra.perp_orth s) (asrt (orth t))
  have e0' : orth t = ovee (asrt (orth t) ≫ s) (asrt (orth t) ≫ orth s) hp0 := by
    rw [← e0, EffectAlgebra.ovee_orth s]; exact ((asrt_spec (orth t)).2).symm
  have hab : asrt (orth t) ≫ s = orth t :=
    ((PCM.ovee_congr rfl hzero hp0 (PCM.perp_zero _)).trans
      (PCM.ovee_zero _ _)).symm.trans e0'.symm
  have habeq : andThen (orth t) s = orth t := hab
  have habsharp : IsSharp (andThen (orth t) s) := by
    rw [habeq]; exact hot
  -- the pristine `l` of 219XI for the pair `(tᵖ, s)`
  obtain ⟨l, hl, hA, hB, h3, h4⟩ := exists_pristine_asrt_comp (orth t) s
  -- `l ∘ asrt_{tᵖ & s} ∘ l† = asrt_{s & tᵖ}`, using `l† ∘ l = asrt_{⌈tᵖ&s⌉}`
  have habsorb1 : asrt (ceilPred (andThen s (orth t))) ≫ asrt (andThen s (orth t))
      = asrt (andThen s (orth t)) :=
    (asrt_absorp_rule (asrt (andThen s (orth t)))
      (isSharp_ceil (andThen s (orth t)))
      (isSharp_ceil (andThen s (orth t)))).2.mp
      (by rw [(asrt_spec (andThen s (orth t))).2]; exact le_ceilPred _)
  have hK : pureDagger l hl ≫ asrt (andThen (orth t) s) ≫ l
      = asrt (andThen s (orth t)) := by
    calc pureDagger l hl ≫ asrt (andThen (orth t) s) ≫ l
        = pureDagger l hl ≫ asrt (orth t) ≫ asrt s := by rw [hA]
      _ = pureDagger l hl ≫ l ≫ asrt (andThen s (orth t)) := by rw [hB]
      _ = (pureDagger l hl ≫ l) ≫ asrt (andThen s (orth t)) := by
            rw [Category.assoc]
      _ = asrt (andThen s (orth t)) := by rw [h4, habsorb1]
  -- the computation of eff.tex:7445–7462
  have habsorb2 : asrt (andThen (orth t) s) ≫ asrt (ceilPred (andThen (orth t) s))
      = asrt (andThen (orth t) s) :=
    (asrt_absorp_rule (asrt (andThen (orth t) s))
      (isSharp_ceil (andThen (orth t) s))
      (isSharp_ceil (andThen (orth t) s))).1.mp
      (by rw [imPred_asrt]; exact pcm_preorder_refl _)
  have hidem : asrt (andThen (orth t) s) ≫ asrt (andThen (orth t) s)
      = asrt (andThen (orth t) s) := (sharp_prop _).2.mp habsharp
  have hsq : asrt (andThen s (orth t)) ≫ asrt (andThen s (orth t))
      = asrt (andThen s (orth t)) := by
    calc asrt (andThen s (orth t)) ≫ asrt (andThen s (orth t))
        = (pureDagger l hl ≫ asrt (andThen (orth t) s) ≫ l) ≫
            (pureDagger l hl ≫ asrt (andThen (orth t) s) ≫ l) := by rw [hK]
      _ = pureDagger l hl ≫ asrt (andThen (orth t) s) ≫
            (l ≫ pureDagger l hl) ≫ asrt (andThen (orth t) s) ≫ l := by
            simp only [Category.assoc]
      _ = pureDagger l hl ≫ (asrt (andThen (orth t) s) ≫
            asrt (ceilPred (andThen (orth t) s))) ≫
            asrt (andThen (orth t) s) ≫ l := by
            rw [h3]; simp only [Category.assoc]
      _ = pureDagger l hl ≫ (asrt (andThen (orth t) s) ≫
            asrt (andThen (orth t) s)) ≫ l := by
            rw [habsorb2]; simp only [Category.assoc]
      _ = pureDagger l hl ≫ asrt (andThen (orth t) s) ≫ l := by rw [hidem]
      _ = asrt (andThen s (orth t)) := hK
  -- so `s & tᵖ` is sharp by `sharp-prop` 208VII
  have hy : IsSharp (andThen s (orth t)) := (sharp_prop _).2.mpr hsq
  -- `(s & t) ⋁ (s & tᵖ) = s & 1 = s` and `s ⋁ sᵖ = 1`, so
  -- `(s & t)ᵖ = (s & tᵖ) ⋁ sᵖ` is sharp by `diamond-oml` 208III
  obtain ⟨hp1, e1⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth t) (asrt s)
  have e1' : s = ovee (asrt s ≫ t) (asrt s ≫ orth t) hp1 := by
    rw [← e1, EffectAlgebra.ovee_orth t]; exact ((asrt_spec s).2).symm
  have hp2 : Perp (ovee (asrt s ≫ t) (asrt s ≫ orth t) hp1) (orth s) := by
    rw [← e1']; exact EffectAlgebra.perp_orth s
  have hw : Perp (asrt s ≫ orth t) (orth s) := PCM.perp_of_ovee_perp hp1 hp2
  have haw : Perp (asrt s ≫ t) (ovee (asrt s ≫ orth t) (orth s) hw) :=
    PCM.perp_ovee_of_ovee_perp hp1 hp2
  have hone : ovee (asrt s ≫ t) (ovee (asrt s ≫ orth t) (orth s) hw) haw = 1 :=
    (PCM.ovee_assoc hp1 hp2).symm.trans
      ((PCM.ovee_congr e1'.symm rfl hp2 (EffectAlgebra.perp_orth s)).trans
        (EffectAlgebra.ovee_orth s))
  have horth : ovee (asrt s ≫ orth t) (orth s) hw = orth (asrt s ≫ t) :=
    EffectAlgebra.orth_unique haw hone
  have hsharp_orth : IsSharp (orth (andThen s t)) := by
    show IsSharp (orth (asrt s ≫ t))
    rw [← horth]
    exact isSharp_ovee hy hos hw
  have hfin := DiamondEffectus.orth_sharp hsharp_orth
  rwa [eabasics_orth_orth] at hfin

/-- **226IV.1** (eff.tex:7466, Definition): the preorder on kernels:
`n ≤ m` when `n` factors through `m` (Grandis; `n ≈ m` when both `n ≤ m`
and `m ≤ n`, and `Nsb A` is the poset of kernels modulo `≈` — the latter
is represented in a ⋄-effectus by `SPred A`, cf. 227III). -/
def KernelLE {W W' X : C} (n : W ⟶ X) (m : W' ⟶ X) : Prop :=
  ∃ f : W ⟶ W', f ≫ m = n

/-- **226IV.2** (eff.tex:7466, Definition): a map `f` is **exact** when the
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

/-- **226V.1** (eff.tex:7506, Theorem): in a †-effectus (in partial form)
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

/-- **226V.2** (eff.tex:7506, Theorem): a map is a cokernel iff it is a
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

/-- **226V.3** (eff.tex:7506, Theorem): a map is exact iff it is
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

/-- **226V** (eff.tex:7506, Theorem): a †-effectus is a pointed
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

/-- **227II.1** (eff.tex:7569, Definition): a composable pair
`A → f → B → g → C` is **exact at** `B` when `ker (cok f) ≈ ker g`.  (In a
†-effectus this amounts to `imᵖ f = ⌈1 ∘ g⌉`, 227III.1.) -/
def ExactAt {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∃ (Q K K' : C) (cf : Y ⟶ Q) (k : K ⟶ Y) (k' : K' ⟶ Y),
    IsCokernel f cf ∧ IsKernel cf k ∧ IsKernel g k' ∧
      KernelLE k k' ∧ KernelLE k' k

/-- **227III.1** (eff.tex:7605, Example): in a †-effectus, `f ∘ g` is
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

/-- **227V** (`diamondboxlemma`, eff.tex:7636, Lemma), first half: in a
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

/-- **227V** (`diamondboxlemma`, eff.tex:7636, Lemma), second half:
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

variable [AndThenEffectus C] [DaggerPrimeEffectus C] {X Y Z : C}

/-! ### The `(–)_⋄`/`(–)^□`-calculus of parsecs 206–208, in the form the
Snake Lemma needs.

The proof of 228II is carried out entirely in the lattices `SPred X` of
sharp predicates and the order adjunctions `f_⋄ ⊣ f^□` between them (this is
227III.3–4: `im f_*(k) = f_⋄(im k)` and `im f^*(k) = f^□(im k)`), so the
following collects the calculus in `SPred`-form: 208IX and 208XII for an
*arbitrary* comprehension resp. quotient, the values of `f_⋄, f^⋄, f^□` at
`0` and `1`, and — the point of 228I's remark that "`l^□` appears where one
would expect `l^⋄`" — the two places where `(–)^□` and `(–)^⋄` do agree:
`π^⋄ = π^□` below `im π`, and `(ξ†)^□ = ξ_⋄` above `ker ξ`.  Both are
instances of the absorption rule 213V for `asrt`, via `π† ∘ π = asrt_{im π}`
and `ξ ∘ ξ† = asrt_{(ker ξ)ᵖ}`. -/

/-- For an isomorphism `θ`, `θ_⋄ ∘ θ^□ = id`. -/
theorem diaPush_boxPull_of_isIso (θ : X ⟶ Y) [IsIso θ] (t : SPred Y) :
    diaPush θ (boxPull θ t) = t :=
  diamondboxlemma_quot (dia_isSharp_zero X) (quotient_basics_3 θ) t

/-- For an isomorphism `θ`, `θ^□ ∘ θ_⋄ = id`. -/
theorem boxPull_diaPush_of_isIso (θ : X ⟶ Y) [IsIso θ] (s : SPred X) :
    boxPull θ (diaPush θ s) = s :=
  diamondboxlemma_compr (compr_basics_3 θ) s

/-- 208IX for an arbitrary comprehension. -/
theorem spred_inf_of_compr {W : C} {s : Pred X} (hs : IsSharp s) {π : W ⟶ X}
    (hπ : IsComprehension s π) (t : SPred X) :
    SPred.IsInf ⟨s, hs⟩ t (diaPush π (boxPull π t)) := by
  obtain ⟨θ, hθ, hcomm, -⟩ := compr_basics_2 hπ (isComprehension_comprMap s)
  have := hθ
  have e : diaPush π (boxPull π t) =
      diaPush (comprMap s) (boxPull (comprMap s) t) := by
    rw [← hcomm, diaPush_comp, boxPull_comp, diaPush_boxPull_of_isIso]
  rw [e]
  exact spred_infimum ⟨s, hs⟩ t

/-- 208XII for an arbitrary quotient. -/
theorem spred_sup_of_quot {Q : C} {s : Pred X} (hs : IsSharp s) {ξ : X ⟶ Q}
    (hξ : IsQuotient s ξ) (t : SPred X) :
    SPred.IsSup ⟨s, hs⟩ t (boxPull ξ (diaPush ξ t)) := by
  obtain ⟨θ, hθ, hcomm, -⟩ := quotient_basics_2 hξ (isQuotient_quotMap s)
  have := hθ
  have e : boxPull ξ (diaPush ξ t) =
      boxPull (quotMap s) (diaPush (quotMap s) t) := by
    rw [← hcomm, diaPush_comp, boxPull_comp, boxPull_diaPush_of_isIso]
  rw [e]
  exact spred_sup ⟨s, hs⟩ t

omit [AndThenEffectus C] [DaggerPrimeEffectus C] in
theorem spred_isSup_unique {s t j j' : SPred X} (h : SPred.IsSup s t j)
    (h' : SPred.IsSup s t j') : j = j' :=
  Subtype.ext (eabasics_le_antisymm (h.2.2 j' h'.1 h'.2.1) (h'.2.2 j h.1 h.2.1))

omit [AndThenEffectus C] [DaggerPrimeEffectus C] in
theorem spred_isInf_unique {s t m m' : SPred X} (h : SPred.IsInf s t m)
    (h' : SPred.IsInf s t m') : m = m' :=
  Subtype.ext (eabasics_le_antisymm (h'.2.2 m h.1 h.2.1) (h.2.2 m' h'.1 h'.2.1))

omit [AndThenEffectus C] [DaggerPrimeEffectus C] in
/-- If `t ≤ s` then `s ∧ t = t`. -/
theorem spred_isInf_eq_right {s t m : SPred X} (h : SPred.IsInf s t m)
    (hts : t.1 ≼ s.1) : m = t :=
  Subtype.ext (eabasics_le_antisymm h.2.1 (h.2.2 t hts (pcm_preorder_refl _)))

omit [AndThenEffectus C] [DaggerPrimeEffectus C] in
/-- If `s = 0` then `s ∨ t = t`. -/
theorem spred_isSup_eq_right {s t j : SPred X} (h : SPred.IsSup s t j)
    (hs : s.1 = 0) : j = t :=
  Subtype.ext (eabasics_le_antisymm
    (h.2.2 t (by rw [hs]; exact zero_le_hom _) (pcm_preorder_refl _)) h.2.1)

omit [DaggerPrimeEffectus C] in
/-- `f^□(1) = 1`. -/
theorem boxPull_one (f : X ⟶ Y) : boxPull f (sOne Y) = sOne X := by
  apply Subtype.ext
  change orth (ceilPred (f ≫ orth (1 : Pred Y))) = (1 : Pred X)
  rw [eabasics_orth_one, FinPAC.comp_zero,
    ceil_of_isSharp (dia_isSharp_zero X), eabasics_orth_zero]

omit [DaggerPrimeEffectus C] in
theorem boxPull_zero_val (f : X ⟶ Y) :
    (boxPull f (sZero Y)).1 = orth (ceilPred (f ≫ truth Y)) := by
  change orth (ceilPred (f ≫ orth (0 : Pred Y))) = _
  rw [eabasics_orth_zero]
  rfl

omit [DaggerPrimeEffectus C] in
theorem diaPull_one_val (f : X ⟶ Y) :
    (diaPull f (sOne Y)).1 = ceilPred (f ≫ truth Y) := rfl

/-- 227III.1 in `SPred` form: `f, g` is exact at the middle object iff
`f_⋄(1) = g^□(0)`. -/
theorem exactAt_iff' (f : X ⟶ Y) (g : Y ⟶ Z) :
    ExactAt f g ↔ diaPush f (sOne X) = boxPull g (sZero Z) := by
  rw [exactAt_iff]
  constructor
  · intro hh
    apply Subtype.ext
    rw [diaPush_one_val, boxPull_zero_val, ← hh, eabasics_orth_orth]
  · intro hh
    have h2 := congrArg Subtype.val hh
    rw [diaPush_one_val, boxPull_zero_val] at h2
    rw [h2, eabasics_orth_orth]

omit [DaggerPrimeEffectus C] in
/-- `s ∨ sᵖ = 1` in `SPred X`. -/
theorem spred_isSup_orth_one (s : SPred X) : SPred.IsSup s s.orth (sOne X) := by
  refine ⟨pred_le_truth _, pred_le_truth _, ?_⟩
  intro r hs ho
  have h1 : orth r.1 ≼ s.1 := by
    have := eabasics_le_iff_orth_le.mp ho
    rwa [spred_orth_val, eabasics_orth_orth] at this
  have h2 : orth r.1 ≼ orth s.1 := eabasics_le_iff_orth_le.mp hs
  have h0 : orth r.1 = 0 := image_sharp_is_order_sharp s.2 h1 h2
  have := congrArg orth h0
  rw [eabasics_orth_orth, eabasics_orth_zero] at this
  rw [this]
  exact pcm_preorder_refl _

omit [DaggerPrimeEffectus C] in
/-- `asrt_t^⋄(y) = y` for sharp `y ≤ t`. -/
theorem diaPull_asrt_self {t : Pred X} (ht : IsSharp t) (y : SPred X)
    (hy : y.1 ≼ t) : diaPull (asrt t) y = y := by
  apply Subtype.ext
  change ceilPred (asrt t ≫ y.1) = y.1
  rw [show asrt t ≫ y.1 = y.1 from (simple_andthen_absorption ht).mp hy]
  exact ceil_of_isSharp y.2

omit [DaggerPrimeEffectus C] in
/-- `asrt_t^□(y) = y` for sharp `y` with `tᵖ ≤ y`. -/
theorem boxPull_asrt_self {t : Pred X} (ht : IsSharp t) (y : SPred X)
    (hy : orth t ≼ y.1) : boxPull (asrt t) y = y := by
  have h1 : orth y.1 ≼ t := by
    have := eabasics_le_iff_orth_le.mp hy
    rwa [eabasics_orth_orth] at this
  change (diaPull (asrt t) y.orth).orth = y
  rw [diaPull_asrt_self ht y.orth h1, spred_orth_orth]

omit [DaggerPrimeEffectus C] in
/-- `asrt_t_⋄(y) = y` for sharp `y ≤ t`. -/
theorem diaPush_asrt_self {t : Pred X} (ht : IsSharp t) (y : SPred X)
    (hy : y.1 ≼ t) : diaPush (asrt t) y = y := by
  rw [← diamond_squares_2 (asrt_spec t).1]
  exact diaPull_asrt_self ht y hy
/-- `π† ∘ π = asrt_s` for a comprehension `π` for a sharp `s`. -/
theorem pureDagger_compr_comp_asrt {W : C} {s : Pred X} (hs : IsSharp s)
    {π : W ⟶ X} (hπ : IsComprehension s π) :
    pureDagger π (isPure_comprehension C hπ) ≫ π = asrt s := by
  obtain ⟨θ, hθ, hcomm, -⟩ := compr_basics_2 hπ (isComprehension_comprMap s)
  have := hθ
  have hθp : IsPure θ := isPure_of_isQuotient (quotient_basics_3 θ)
  have hπsp : IsPure (comprMap s) :=
    isPure_comprehension C (isComprehension_comprMap s)
  have hd : pureDagger π (isPure_comprehension C hπ) =
      pureDagger (comprMap s) hπsp ≫ pureDagger θ hθp :=
    (pureDagger_congr _ (upm_closed_pure hθp hπsp) hcomm.symm).trans
      (dagger_is_functor hθp hπsp)
  have hdπs : pureDagger (comprMap s) hπsp = zetaMap s hs :=
    pureDagger_eq _ (dagger_prime_basics_pi hs)
  have hdθ : pureDagger θ hθp = inv θ :=
    pureDagger_eq _ (dagger_prime_basics_iso (asIso θ))
  rw [hd, hdπs, hdθ, ← hcomm, Category.assoc, ← Category.assoc (inv θ) θ,
    IsIso.inv_hom_id, Category.id_comp]
  exact (zetaMap_spec s hs).2.2

/-- `ξ ∘ ξ† = asrt_{sᵖ}` for a quotient `ξ` for a sharp `s`. -/
theorem pureDagger_quot_comp_asrt {Q : C} {s : Pred X} (hs : IsSharp s)
    {ξ : X ⟶ Q} (hξ : IsQuotient s ξ) :
    ξ ≫ pureDagger ξ (isPure_of_isQuotient hξ) = asrt (orth s) := by
  have hs' : IsSharp (orth s) := DiamondEffectus.orth_sharp hs
  obtain ⟨hq, hπζ, hζπ⟩ := zetaMap_spec (orth s) hs'
  have hq' : IsQuotient s (zetaMap (orth s) hs') := by
    rwa [eabasics_orth_orth] at hq
  obtain ⟨θ, hθ, hcomm, -⟩ := quotient_basics_2 hξ hq'
  have := hθ
  have hθp : IsPure θ := isPure_of_isQuotient (quotient_basics_3 θ)
  have hζp : IsPure (zetaMap (orth s) hs') := isPure_of_isQuotient hq
  have hd : pureDagger ξ (isPure_of_isQuotient hξ) =
      pureDagger θ hθp ≫ pureDagger (zetaMap (orth s) hs') hζp :=
    (pureDagger_congr _ (upm_closed_pure hζp hθp) hcomm.symm).trans
      (dagger_is_functor hζp hθp)
  have hdζ : pureDagger (zetaMap (orth s) hs') hζp = comprMap (orth s) :=
    pureDagger_eq _ (dagger_prime_basics_zeta hs')
  have hdθ : pureDagger θ hθp = inv θ :=
    pureDagger_eq _ (dagger_prime_basics_iso (asIso θ))
  rw [hd, hdζ, hdθ, ← hcomm, Category.assoc, ← Category.assoc θ (inv θ),
    IsIso.hom_inv_id, Category.id_comp]
  exact hζπ

omit [DaggerPrimeEffectus C] in
/-- A pure map with image `1` and sharp `1 ∘ f` is a quotient. -/
theorem isQuotient_of_pure {f : X ⟶ Y} (hf : IsPure f) (him : imPred f = 1)
    (hs : IsSharp (f ≫ truth Y)) : IsQuotient (orth (f ≫ truth Y)) f := by
  obtain ⟨β, hform⟩ :=
    standard_form_of_eq hf hs (isSharp_one Y) (ceil_of_isSharp hs) him
  have hζ1 : zetaMap (f ≫ truth Y) hs ≫ truth (comprObj (f ≫ truth Y)) =
      f ≫ truth Y := by
    rw [quotient_basics_5 (zetaMap_spec (f ≫ truth Y) hs).1, eabasics_orth_orth]
  have habs : asrt (f ≫ truth Y) ≫ zetaMap (f ≫ truth Y) hs =
      zetaMap (f ≫ truth Y) hs :=
    (asrt_absorp_rule (zetaMap (f ≫ truth Y) hs) (isSharp_one _) hs).2.mp
      (by rw [hζ1]; exact pcm_preorder_refl _)
  have hiso : IsIso (comprMap (1 : Pred Y)) := isIso_comprMap_one Y
  have hform' : f = zetaMap (f ≫ truth Y) hs ≫ (β.hom ≫ comprMap (1 : Pred Y)) :=
    hform.trans (by rw [← Category.assoc, habs])
  have hq : IsQuotient (orth (f ≫ truth Y))
      (zetaMap (f ≫ truth Y) hs ≫ (β.hom ≫ comprMap (1 : Pred Y))) :=
    quotient_basics_1 (zetaMap_spec (f ≫ truth Y) hs).1 _
  rwa [← hform'] at hq

/-- For a quotient `ξ` for a sharp `s` and sharp `y ≥ s`, `(ξ†)^□(y) = ξ_⋄(y)`. -/
theorem boxPull_pureDagger_quot {Q : C} {s : Pred X} (hs : IsSharp s)
    {ξ : X ⟶ Q} (hξ : IsQuotient s ξ) (y : SPred X) (hy : s ≼ y.1) :
    boxPull (pureDagger ξ (isPure_of_isQuotient hξ)) y = diaPush ξ y := by
  have hs' : IsSharp (orth s) := DiamondEffectus.orth_sharp hs
  have key : boxPull ξ (boxPull (pureDagger ξ (isPure_of_isQuotient hξ)) y) = y := by
    rw [← boxPull_comp, pureDagger_quot_comp_asrt hs hξ]
    exact boxPull_asrt_self hs' y (by rwa [eabasics_orth_orth])
  calc boxPull (pureDagger ξ (isPure_of_isQuotient hξ)) y
      = diaPush ξ (boxPull ξ (boxPull (pureDagger ξ (isPure_of_isQuotient hξ)) y)) :=
        (diamondboxlemma_quot hs hξ _).symm
    _ = diaPush ξ y := by rw [key]

/-- For a comprehension `π` for a sharp `s` and sharp `y ≤ s`,
`π^⋄(y) = π^□(y)`. -/
theorem diaPull_eq_boxPull_compr {W : C} {s : Pred X} (hs : IsSharp s)
    {π : W ⟶ X} (hπ : IsComprehension s π) (y : SPred X) (hy : y.1 ≼ s) :
    diaPull π y = boxPull π y := by
  have h1 : diaPush π (diaPull π y) = y := by
    rw [pureDagger_diamond_adjoint (isPure_comprehension C hπ), ← diaPush_comp,
      pureDagger_compr_comp_asrt hs hπ]
    exact diaPush_asrt_self hs y hy
  calc diaPull π y = boxPull π (diaPush π (diaPull π y)) :=
        (diamondboxlemma_compr hπ _).symm
    _ = boxPull π y := by rw [h1]

omit [DaggerPrimeEffectus C] in
/-- Quotients have image `1`. -/
theorem imPred_of_isQuotient {Q : C} {s : Pred X} {ξ : X ⟶ Q}
    (hξ : IsQuotient s ξ) : imPred ξ = 1 := by
  have := quotient_basics_6 hξ
  exact (cancel_epi ξ).mp (isImage_imPred ξ).1

omit [DaggerPrimeEffectus C] in
/-- A quotient is "surjective": `ξ_⋄(1) = 1`. -/
theorem diaPush_one_of_isQuotient {Q : C} {s : Pred X} {ξ : X ⟶ Q}
    (hξ : IsQuotient s ξ) : diaPush ξ (sOne X) = sOne Q :=
  Subtype.ext (by rw [diaPush_one_val, imPred_of_isQuotient hξ]; rfl)
omit [DaggerPrimeEffectus C] in
theorem comprMap_zero (X : C) : comprMap (0 : Pred X) = 0 := by
  have h := (isComprehension_comprMap (0 : Pred X)).1
  rw [FinPAC.comp_zero] at h
  exact EffectusPartialForm.eq_zero_of_one_zero h.symm

omit [DaggerPrimeEffectus C] in
theorem diaPush_zero (f : X ⟶ Y) : diaPush f (sZero X) = sZero Y := by
  apply Subtype.ext
  change imPred (comprMap (0 : Pred X) ≫ f) = (0 : Pred Y)
  rw [comprMap_zero, FinPAC.zero_comp, imPred_zero]

omit [DaggerPrimeEffectus C] in
theorem boxPull_zero_of_isTotal {f : X ⟶ Y} (hf : IsTotal f) :
    boxPull f (sZero Y) = sZero X := by
  apply Subtype.ext
  rw [boxPull_zero_val, hf]
  change orth (ceilPred (1 : Pred X)) = 0
  rw [ceil_of_isSharp (isSharp_one X), eabasics_orth_one]

omit [DaggerPrimeEffectus C] in
theorem spred_orth_zero (X : C) : (sZero X).orth = sOne X :=
  Subtype.ext eabasics_orth_zero

omit [DaggerPrimeEffectus C] in
theorem imPred_comprMap_orth (q : Pred X) :
    imPred (comprMap (orth q)) = orth (ceilPred q) := by
  change floorPred (orth q) = orth (ceilPred q)
  rw [show ceilPred q = orth (floorPred (orth q)) from rfl, eabasics_orth_orth]

omit [DaggerPrimeEffectus C] in
/-- The standard kernel of `u` has image `u^□(0)`. -/
theorem diaPush_kerCompr_one (u : X ⟶ Y) :
    diaPush (comprMap (orth (u ≫ truth Y))) (sOne (comprObj (orth (u ≫ truth Y))))
      = boxPull u (sZero Y) :=
  Subtype.ext (by rw [diaPush_one_val, boxPull_zero_val, imPred_comprMap_orth])

omit [DaggerPrimeEffectus C] in
theorem comp_pred_eq_of_im_le {u : X ⟶ Y} {p : Pred Y} (hle : imPred u ≼ p) :
    u ≫ p = u ≫ truth Y :=
  eabasics_le_antisymm (comp_le_comp u (pred_le_truth p))
    (by rw [← (isImage_imPred u).1]; exact comp_le_comp u hle)

/-- `(f†)^⋄ = f_⋄`. -/
theorem diaPull_pureDagger {f : X ⟶ Y} (hf : IsPure f) :
    diaPull (pureDagger f hf) = diaPush f := by
  have h := pureDagger_diamond_adjoint (isPure_pureDagger hf)
  rwa [dagger_idempotent hf] at h

omit [DaggerPrimeEffectus C] in
theorem spred_eq_zero {s : SPred X} (h : s.1 ≼ 0) : s = sZero X :=
  Subtype.ext (eq_zero_of_le_zero h)

omit [AndThenEffectus C] [DaggerPrimeEffectus C] in
/-- If `t = 0` then `s ∨ t = s`. -/
theorem spred_isSup_eq_left {s t j : SPred X} (h : SPred.IsSup s t j)
    (ht : t.1 = 0) : j = s :=
  Subtype.ext (eabasics_le_antisymm
    (h.2.2 s (pcm_preorder_refl _) (by rw [ht]; exact zero_le_hom _)) h.1)

/-- `(f†)_⋄ = f^⋄`. -/
theorem diaPush_pureDagger {f : X ⟶ Y} (hf : IsPure f) :
    diaPush (pureDagger f hf) = diaPull f :=
  (pureDagger_diamond_adjoint hf).symm

/-- `(f†)^□(0) = f_⋄(1)ᵖ`. -/
theorem boxPull_pureDagger_zero {f : X ⟶ Y} (hf : IsPure f) :
    boxPull (pureDagger f hf) (sZero X) = (diaPush f (sOne X)).orth := by
  change (diaPull (pureDagger f hf) (sZero X).orth).orth = _
  rw [diaPull_pureDagger hf, spred_orth_zero]

/-- **228II** (eff.tex:7670, Snake Lemma; Grandis): suppose the diagram

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
        ExactAt hbar kbar := by
  -- The route (see PROVING-LOG, session 11): only the *left* face of the cube
  -- of 228III is built — the comprehension `m = π_{g^□(c^□(0))}`, the sharp
  -- quotient `g' = m ∘ g ∘ c_π†`, the lift `b'` of `b` along `m` and `h`, and
  -- `d` as the lift of `b' ∘ a_ζ` along `g'`.  The four exactness statements
  -- are `u_⋄(1) = w^□(0)` (227III.1, `exactAt_iff'`), so `d` is only ever met
  -- at `1` and at `0`, and the right face (`v`, `h'`) together with three of
  -- the four forms of the thesis's `snakedidents` is never needed.
  obtain ⟨sg, hsg, hgq⟩ := hg
  obtain ⟨ph, hh0⟩ := hh
  have hhc : IsComprehension (imPred h) h := isComprehension_imPred hh0
  have hHi : IsSharp (imPred h) := isSharp_imPred C h
  have hAi : IsSharp (imPred a) := isSharp_imPred C a
  have hBi : IsSharp (imPred b) := isSharp_imPred C b
  have hCi : IsSharp (imPred c) := isSharp_imPred C c
  have hgp : IsPure g := isPure_of_isQuotient hgq
  -- images as sharp predicates
  have hIa : diaPush a (sOne A) = (⟨imPred a, hAi⟩ : SPred A') :=
    Subtype.ext (diaPush_one_val a)
  have hIb : diaPush b (sOne B) = (⟨imPred b, hBi⟩ : SPred B') :=
    Subtype.ext (diaPush_one_val b)
  have hIc : diaPush c (sOne C₃) = (⟨imPred c, hCi⟩ : SPred C₃') :=
    Subtype.ext (diaPush_one_val c)
  have hIh : diaPush h (sOne A') = (⟨imPred h, hHi⟩ : SPred B') :=
    Subtype.ext (diaPush_one_val h)
  have hIf : diaPush f (sOne A) = (⟨imPred f, isSharp_imPred C f⟩ : SPred B) :=
    Subtype.ext (diaPush_one_val f)
  have hKB : boxPull b (sZero B') =
      SPred.orth ⟨ceilPred (b ≫ truth B'), isSharp_ceil _⟩ :=
    Subtype.ext (boxPull_zero_val b)
  -- kernels of the cokernels
  have hKa : boxPull (quotMap (imPred a)) (sZero (quotObj (imPred a))) =
      diaPush a (sOne A) :=
    Subtype.ext (by
      rw [boxPull_zero_of_isQuotient hAi (isQuotient_quotMap _), diaPush_one_val])
  have hKb : boxPull (quotMap (imPred b)) (sZero (quotObj (imPred b))) =
      diaPush b (sOne B) :=
    Subtype.ext (by
      rw [boxPull_zero_of_isQuotient hBi (isQuotient_quotMap _), diaPush_one_val])
  have hKc : boxPull (quotMap (imPred c)) (sZero (quotObj (imPred c))) =
      diaPush c (sOne C₃) :=
    Subtype.ext (by
      rw [boxPull_zero_of_isQuotient hCi (isQuotient_quotMap _), diaPush_one_val])
  -- exactness of the rows
  have r₁ : diaPush f (sOne A) = boxPull g (sZero C₃) := (exactAt_iff' f g).mp row₁
  have r₂ : diaPush h (sOne A') = boxPull k (sZero C₃') := (exactAt_iff' h k).mp row₂
  -- the modularity conditions, restated
  have M1 : SPred.IsSup (boxPull b (sZero B')) (diaPush f (sOne A))
      (boxPull b (diaPush b (diaPush f (sOne A)))) := by
    have hx := m₁; rw [← hKB, ← hIf] at hx; exact hx
  have M2 : SPred.IsInf (diaPush h (sOne A')) (diaPush b (sOne B))
      (diaPush b (boxPull b (diaPush h (sOne A')))) := by
    have hx := m₂; rw [← hIh, ← hIb] at hx; exact hx
  have M3 : SPred.IsSup (diaPush h (sOne A')) (diaPush b (sOne B))
      (boxPull k (diaPush k (diaPush b (sOne B)))) := by
    have hx := m₃; rw [← hIh, ← hIb] at hx; exact hx
  have M4₀ : SPred.IsInf (boxPull b (sZero B')) (diaPush f (sOne A))
      (diaPush f (boxPull f (boxPull b (sZero B')))) := by
    have hx := m₄; rw [← hKB, ← hIf] at hx; exact hx
  -- `f^□(ker b) = ker a`
  have hfka : boxPull f (boxPull b (sZero B')) = boxPull a (sZero A') := by
    rw [← boxPull_comp, w₁, boxPull_comp, boxPull_zero_of_isTotal (compr_total hh0)]
  have M4 : SPred.IsInf (boxPull b (sZero B')) (diaPush f (sOne A))
      (diaPush f (boxPull a (sZero A'))) := by rw [← hfka]; exact M4₀
  -- `h_⋄(im a) = b_⋄(im f) ≤ im b`
  have hcomm₁ : diaPush h (diaPush a (sOne A)) = diaPush b (diaPush f (sOne A)) := by
    rw [← diaPush_comp, ← diaPush_comp, w₁]
  have hab : (diaPush h (diaPush a (sOne A))).1 ≼ (diaPush b (sOne B)).1 := by
    rw [hcomm₁]
    exact order_adj_basics_1 b (pred_le_truth _)
  have hAih : (diaPush a (sOne A)).1 ≼ (boxPull h (diaPush b (sOne B))).1 :=
    (diamond_adjunction' h _ _).mp hab
  -- `b_⋄(ker b) = 0`
  have hbkb : diaPush b (boxPull b (sZero B')) = sZero B' :=
    spred_eq_zero (diaPush_boxPull_le b (sZero B'))
  -- `g_⋄(ker b) ≤ ker c`
  have hgkb : (diaPush g (boxPull b (sZero B'))).1 ≼ (boxPull c (sZero C₃')).1 := by
    refine (diamond_adjunction' c _ _).mp ?_
    have e : diaPush c (diaPush g (boxPull b (sZero B'))) =
        diaPush k (diaPush b (boxPull b (sZero B'))) := by
      rw [← diaPush_comp, ← diaPush_comp, w₂]
    rw [e, hbkb, diaPush_zero]
    exact pcm_preorder_refl _
  -- the standard kernel of `c` is a comprehension for `c^□(0)`
  have hcπ : IsComprehension (boxPull c (sZero C₃')).1
      (comprMap (orth (c ≫ truth C₃'))) := by
    have hx := isComprehension_imPred (isComprehension_comprMap (orth (c ≫ truth C₃')))
    rwa [imPred_comprMap_orth, ← boxPull_zero_val] at hx
  have hbπ : IsComprehension (boxPull b (sZero B')).1
      (comprMap (orth (b ≫ truth B'))) := by
    have hx := isComprehension_imPred (isComprehension_comprMap (orth (b ≫ truth B')))
    rwa [imPred_comprMap_orth, ← boxPull_zero_val] at hx
  -- ### the left face of the cube: `m` and `g'`
  obtain ⟨M, hM⟩ : ∃ M : SPred B, M = boxPull g (boxPull c (sZero C₃')) := ⟨_, rfl⟩
  have hm : IsComprehension M.1 (comprMap M.1) := isComprehension_comprMap M.1
  have hmp : IsPure (comprMap M.1) := isPure_comprehension C hm
  have hdm1 : diaPush (comprMap M.1) (sOne (comprObj M.1)) = M :=
    Subtype.ext (by rw [diaPush_one_val]; exact (img_of_compr M.1).2 M.1 M.2)
  have hMb : M = boxPull b (diaPush h (sOne A')) := by
    rw [hM, ← boxPull_comp, w₂, boxPull_comp, ← r₂]
  have himg : imPred (comprMap M.1 ≫ g) ≼ (boxPull c (sZero C₃')).1 := by
    have e : diaPush (comprMap M.1 ≫ g) (sOne (comprObj M.1)) = diaPush g M := by
      rw [diaPush_comp, hdm1]
    have h2 : (diaPush g M).1 ≼ (boxPull c (sZero C₃')).1 := by
      rw [hM]; exact diaPush_boxPull_le g _
    rw [← diaPush_one_val, e]
    exact h2
  obtain ⟨g', hg'def⟩ : ∃ g' : comprObj M.1 ⟶ comprObj (orth (c ≫ truth C₃')),
      g' = comprMap M.1 ≫ g ≫ pureDagger (comprMap (orth (c ≫ truth C₃')))
        (isPure_comprehension C (isComprehension_comprMap _)) := ⟨_, rfl⟩
  have hcd : pureDagger (comprMap (orth (c ≫ truth C₃')))
      (isPure_comprehension C (isComprehension_comprMap _)) ≫
      comprMap (orth (c ≫ truth C₃')) = asrt (boxPull c (sZero C₃')).1 :=
    pureDagger_compr_comp_asrt (boxPull c (sZero C₃')).2 hcπ
  have hsq : g' ≫ comprMap (orth (c ≫ truth C₃')) = comprMap M.1 ≫ g := by
    rw [hg'def, Category.assoc, Category.assoc, hcd, ← Category.assoc]
    exact (asrt_absorp_rule (comprMap M.1 ≫ g) (boxPull c (sZero C₃')).2
      (isSharp_one _)).1.mp himg
  -- `g'` is a sharp quotient
  have hkerle : ∀ (K : C) (kq : K ⟶ B), IsKernel g kq → KernelLE kq (comprMap M.1) := by
    intro K kq hkq
    obtain ⟨θ, hθ, hcomm⟩ :=
      isKernel_unique hkq (effectus_kernels g (isComprehension_comprMap (orth (g ≫ truth C₃))))
    have him : imPred kq ≼ M.1 := by
      have e : imPred kq = (boxPull g (sZero C₃)).1 := by
        rw [← hcomm, (im_ineq (comprMap (orth (g ≫ truth C₃))) θ).2 θ hθ,
          imPred_comprMap_orth, ← boxPull_zero_val]
      rw [e, hM]
      exact (exc_diam_order_pres g (zero_le_hom (boxPull c (sZero C₃')).1)).2
    obtain ⟨u, hu, -⟩ := hm.2 kq (comp_pred_eq_of_im_le him)
    exact ⟨u, hu⟩
  have hprist : Pristine (comprMap M.1 ≫ g) :=
    (homological_exact _).mp
      (homological_category.2.2 (comprMap M.1) g
        ⟨_, _, (compr_is_kernel M.1 _).mp hm⟩ ⟨_, _, (exc_cokernels hsg g).mp hgq⟩
        hkerle)
  have hg'truth : g' ≫ truth (comprObj (orth (c ≫ truth C₃'))) =
      (comprMap M.1 ≫ g) ≫ truth C₃ := by
    rw [← hsq, Category.assoc, compr_total (isComprehension_comprMap _)]
  have hg'sharp : IsSharp (g' ≫ truth (comprObj (orth (c ≫ truth C₃')))) := by
    rw [hg'truth]; exact hprist.2
  have hg'pure : IsPure g' := by
    rw [hg'def]
    exact upm_closed_pure hmp (upm_closed_pure hgp (isPure_pureDagger _))
  have hg'one : diaPush g' (sOne (comprObj M.1)) =
      sOne (comprObj (orth (c ≫ truth C₃'))) := by
    have e1 : diaPush (comprMap (orth (c ≫ truth C₃')))
        (diaPush g' (sOne (comprObj M.1))) = boxPull c (sZero C₃') := by
      rw [← diaPush_comp, hsq, diaPush_comp, hdm1, hM,
        diamondboxlemma_quot hsg hgq]
    have e2 : diaPush (comprMap (orth (c ≫ truth C₃')))
        (sOne (comprObj (orth (c ≫ truth C₃')))) = boxPull c (sZero C₃') :=
      diaPush_kerCompr_one c
    calc diaPush g' (sOne (comprObj M.1))
        = boxPull (comprMap (orth (c ≫ truth C₃')))
            (diaPush (comprMap (orth (c ≫ truth C₃')))
              (diaPush g' (sOne (comprObj M.1)))) :=
          (diamondboxlemma_compr hcπ _).symm
      _ = boxPull (comprMap (orth (c ≫ truth C₃')))
            (diaPush (comprMap (orth (c ≫ truth C₃')))
              (sOne (comprObj (orth (c ≫ truth C₃'))))) := by rw [e1, e2]
      _ = sOne (comprObj (orth (c ≫ truth C₃'))) := diamondboxlemma_compr hcπ _
  have hg'q : IsQuotient (orth (g' ≫ truth (comprObj (orth (c ≫ truth C₃'))))) g' :=
    isQuotient_of_pure hg'pure
      (by rw [← diaPush_one_val, hg'one]; rfl) hg'sharp
  have hg'ssharp : IsSharp (orth (g' ≫ truth (comprObj (orth (c ≫ truth C₃')))))  :=
    DiamondEffectus.orth_sharp hg'sharp
  -- ### the lift `b'` of `b` along `m` and `h`
  have hmb : (diaPush b M).1 ≼ imPred h := by
    rw [hMb, ← diaPush_one_val h]
    exact diaPush_boxPull_le b _
  obtain ⟨b', hb'comm, -⟩ := hhc.2 (comprMap M.1 ≫ b)
    (comp_pred_eq_of_im_le (by
      rw [← diaPush_one_val, diaPush_comp, hdm1]; exact hmb))
  -- `b'^□ ∘ h^□ = m^□ ∘ b^□`
  have hb'box : ∀ y : SPred B', boxPull b' (boxPull h y) =
      boxPull (comprMap M.1) (boxPull b y) := by
    intro y
    rw [← boxPull_comp, hb'comm, boxPull_comp]
  -- ### the connecting map `d`
  have hb'Ai : boxPull b' (diaPush a (sOne A)) =
      boxPull (comprMap M.1) (boxPull b (diaPush b (diaPush f (sOne A)))) := by
    have e : boxPull h (diaPush h (diaPush a (sOne A))) = diaPush a (sOne A) :=
      diamondboxlemma_compr hhc _
    rw [← e, hb'box, hcomm₁]
  have hdcond : ((b' ≫ quotMap (imPred a)) ≫ truth (quotObj (imPred a))) ≼
      orth (orth (g' ≫ truth (comprObj (orth (c ≫ truth C₃'))))) := by
    rw [eabasics_orth_orth]
    -- `g'^□(0) ≤ (b' ∘ a_ζ)^□(0)`
    have e1 : boxPull g' (sZero (comprObj (orth (c ≫ truth C₃')))) =
        boxPull (comprMap M.1) (boxPull g (sZero C₃)) := by
      have e : boxPull g' (boxPull (comprMap (orth (c ≫ truth C₃'))) (sZero C₃)) =
          boxPull (comprMap M.1) (boxPull g (sZero C₃)) := by
        rw [← boxPull_comp, hsq, boxPull_comp]
      rwa [boxPull_zero_of_isTotal (compr_total (isComprehension_comprMap _))] at e
    have e2 : boxPull (b' ≫ quotMap (imPred a)) (sZero (quotObj (imPred a))) =
        boxPull (comprMap M.1) (boxPull b (diaPush b (diaPush f (sOne A)))) := by
      rw [boxPull_comp, hKa, hb'Ai]
    have e3 : (boxPull g' (sZero (comprObj (orth (c ≫ truth C₃'))))).1 ≼
        (boxPull (b' ≫ quotMap (imPred a)) (sZero (quotObj (imPred a)))).1 := by
      rw [e1, e2]
      refine (exc_diam_order_pres (comprMap M.1) ?_).2
      rw [← r₁]
      exact le_boxPull_diaPush b _
    -- turn the inequality of kernels into one of truths
    rw [boxPull_zero_val, boxPull_zero_val] at e3
    have e4 : ceilPred ((b' ≫ quotMap (imPred a)) ≫ truth (quotObj (imPred a))) ≼
        ceilPred (g' ≫ truth (comprObj (orth (c ≫ truth C₃')))) := by
      have := eabasics_le_iff_orth_le.mp e3
      rwa [eabasics_orth_orth, eabasics_orth_orth] at this
    refine pcm_preorder_trans (le_ceil _) ?_
    rw [← ceil_of_isSharp hg'sharp]
    exact e4
  obtain ⟨d, hd, -⟩ := hg'q.2 (b' ≫ quotMap (imPred a)) hdcond
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · -- ### exactness at `ker b`
    rw [exactAt_iff']
    have hlhs : diaPush (comprMap (orth (a ≫ truth A')) ≫ f ≫
        pureDagger (comprMap (orth (b ≫ truth B')))
          (isPure_comprehension C (isComprehension_comprMap _)))
        (sOne (comprObj (orth (a ≫ truth A')))) =
        boxPull (comprMap (orth (b ≫ truth B'))) (diaPush f (boxPull a (sZero A'))) := by
      rw [diaPush_comp, diaPush_comp, diaPush_kerCompr_one, diaPush_pureDagger]
      exact diaPull_eq_boxPull_compr (boxPull b (sZero B')).2 hbπ _ M4.1
    have hrhs : boxPull (comprMap (orth (b ≫ truth B')) ≫ g ≫
        pureDagger (comprMap (orth (c ≫ truth C₃')))
          (isPure_comprehension C (isComprehension_comprMap _)))
        (sZero (comprObj (orth (c ≫ truth C₃')))) =
        boxPull (comprMap (orth (b ≫ truth B')))
          (boxPull g (boxPull c (sZero C₃')).orth) := by
      rw [boxPull_comp, boxPull_comp, boxPull_pureDagger_zero, diaPush_kerCompr_one]
    rw [hlhs, hrhs]
    have hV : SPred.IsInf (boxPull b (sZero B'))
        (boxPull g (boxPull c (sZero C₃')).orth)
        (diaPush f (boxPull a (sZero A'))) := by
      refine ⟨M4.1, ?_, ?_⟩
      · have h1 : (diaPush f (boxPull a (sZero A'))).1 ≼ (boxPull g (sZero C₃)).1 := by
          rw [← r₁]; exact order_adj_basics_1 f (pred_le_truth _)
        refine (diamond_adjunction' g _ _).mp ?_
        refine pcm_preorder_trans (order_adj_basics_1 g h1) ?_
        rw [spred_eq_zero (diaPush_boxPull_le g (sZero C₃))]
        exact zero_le_hom _
      · intro r hr1 hr2
        have h1 : (diaPush g r).1 ≼ ((boxPull c (sZero C₃')).orth).1 :=
          (diamond_adjunction' g r _).mpr hr2
        have h2 : (diaPush g r).1 ≼ (boxPull c (sZero C₃')).1 :=
          pcm_preorder_trans (order_adj_basics_1 g hr1) hgkb
        have h3 : (diaPush g r).1 = 0 :=
          image_sharp_is_order_sharp (boxPull c (sZero C₃')).2 h2 h1
        have h4 : r.1 ≼ (boxPull g (sZero C₃)).1 :=
          (diamond_adjunction' g r (sZero C₃)).mp (by rw [h3]; exact zero_le_hom _)
        rw [← r₁] at h4
        exact M4.2.2 r hr1 h4
    have e1 : diaPush (comprMap (orth (b ≫ truth B')))
        (boxPull (comprMap (orth (b ≫ truth B'))) (diaPush f (boxPull a (sZero A')))) =
        diaPush f (boxPull a (sZero A')) :=
      spred_isInf_eq_right (spred_inf_of_compr (boxPull b (sZero B')).2 hbπ _) M4.1
    have e2 : diaPush (comprMap (orth (b ≫ truth B')))
        (boxPull (comprMap (orth (b ≫ truth B')))
          (boxPull g (boxPull c (sZero C₃')).orth)) =
        diaPush f (boxPull a (sZero A')) :=
      spred_isInf_unique (spred_inf_of_compr (boxPull b (sZero B')).2 hbπ _) hV
    calc boxPull (comprMap (orth (b ≫ truth B'))) (diaPush f (boxPull a (sZero A')))
        = boxPull (comprMap (orth (b ≫ truth B')))
            (diaPush (comprMap (orth (b ≫ truth B')))
              (boxPull (comprMap (orth (b ≫ truth B')))
                (diaPush f (boxPull a (sZero A'))))) :=
          (order_adj_basics_6 _ _).symm
      _ = boxPull (comprMap (orth (b ≫ truth B')))
            (diaPush (comprMap (orth (b ≫ truth B')))
              (boxPull (comprMap (orth (b ≫ truth B')))
                (boxPull g (boxPull c (sZero C₃')).orth))) := by rw [e1, e2]
      _ = boxPull (comprMap (orth (b ≫ truth B')))
            (boxPull g (boxPull c (sZero C₃')).orth) := order_adj_basics_6 _ _
  · -- ### exactness at `ker c`
    rw [exactAt_iff']
    have hlhs : diaPush (comprMap (orth (b ≫ truth B')) ≫ g ≫
        pureDagger (comprMap (orth (c ≫ truth C₃')))
          (isPure_comprehension C (isComprehension_comprMap _)))
        (sOne (comprObj (orth (b ≫ truth B')))) =
        boxPull (comprMap (orth (c ≫ truth C₃')))
          (diaPush g (boxPull b (sZero B'))) := by
      rw [diaPush_comp, diaPush_comp, diaPush_kerCompr_one, diaPush_pureDagger]
      exact diaPull_eq_boxPull_compr (boxPull c (sZero C₃')).2 hcπ _ hgkb
    have hzM : (boxPull b (diaPush b (diaPush f (sOne A)))).1 ≼ M.1 := by
      refine M1.2.2 M ?_ ?_
      · have hx := (diamond_adjunction' g (boxPull b (sZero B'))
          (boxPull c (sZero C₃'))).mp hgkb
        rw [← hM] at hx
        exact hx
      · rw [r₁, hM]
        exact (exc_diam_order_pres g (zero_le_hom (boxPull c (sZero C₃')).1)).2
    have hgz : diaPush g (boxPull b (diaPush b (diaPush f (sOne A)))) =
        diaPush g (boxPull b (sZero B')) := by
      refine spred_isSup_eq_left (order_adj_basics_2 g M1) ?_
      have hx : diaPush g (diaPush f (sOne A)) = sZero C₃ := by
        rw [r₁]
        exact spred_eq_zero (diaPush_boxPull_le g (sZero C₃))
      rw [hx]
      rfl
    have hrhs : boxPull d (sZero (quotObj (imPred a))) =
        diaPush g' (boxPull (comprMap M.1)
          (boxPull b (diaPush b (diaPush f (sOne A))))) := by
      have e : boxPull g' (boxPull d (sZero (quotObj (imPred a)))) =
          boxPull (comprMap M.1) (boxPull b (diaPush b (diaPush f (sOne A)))) := by
        rw [← boxPull_comp, hd, boxPull_comp, hKa, hb'Ai]
      calc boxPull d (sZero (quotObj (imPred a)))
          = diaPush g' (boxPull g' (boxPull d (sZero (quotObj (imPred a))))) :=
            (diamondboxlemma_quot hg'ssharp hg'q _).symm
        _ = _ := by rw [e]
    rw [hlhs, hrhs]
    have inj : ∀ u v : SPred (comprObj (orth (c ≫ truth C₃'))),
        diaPush (comprMap (orth (c ≫ truth C₃'))) u =
          diaPush (comprMap (orth (c ≫ truth C₃'))) v → u = v := by
      intro u v huv
      rw [← diamondboxlemma_compr hcπ u, huv, diamondboxlemma_compr hcπ v]
    refine inj _ _ ?_
    have e1 : diaPush (comprMap (orth (c ≫ truth C₃')))
        (boxPull (comprMap (orth (c ≫ truth C₃')))
          (diaPush g (boxPull b (sZero B')))) = diaPush g (boxPull b (sZero B')) :=
      spred_isInf_eq_right (spred_inf_of_compr (boxPull c (sZero C₃')).2 hcπ _) hgkb
    have e2 : diaPush (comprMap (orth (c ≫ truth C₃')))
        (diaPush g' (boxPull (comprMap M.1)
          (boxPull b (diaPush b (diaPush f (sOne A)))))) =
        diaPush g (boxPull b (sZero B')) := by
      rw [← diaPush_comp, hsq, diaPush_comp,
        spred_isInf_eq_right (spred_inf_of_compr M.2 hm _) hzM, hgz]
    rw [e1, e2]
  · -- ### exactness at `cok a`
    rw [exactAt_iff']
    have hinf2 : SPred.IsInf (diaPush h (sOne A')) (diaPush b (sOne B))
        (diaPush h (boxPull h (diaPush b (sOne B)))) := by
      rw [hIh]; exact spred_inf_of_compr hHi hhc _
    have hb'one : diaPush b' (sOne (comprObj M.1)) = boxPull h (diaPush b (sOne B)) := by
      have e1 : diaPush h (diaPush b' (sOne (comprObj M.1))) = diaPush b M := by
        rw [← diaPush_comp, hb'comm, diaPush_comp, hdm1]
      have e2 : diaPush b M = diaPush h (boxPull h (diaPush b (sOne B))) := by
        rw [hMb]; exact spred_isInf_unique M2 hinf2
      calc diaPush b' (sOne (comprObj M.1))
          = boxPull h (diaPush h (diaPush b' (sOne (comprObj M.1)))) :=
            (diamondboxlemma_compr hhc _).symm
        _ = boxPull h (diaPush h (boxPull h (diaPush b (sOne B)))) := by rw [e1, e2]
        _ = boxPull h (diaPush b (sOne B)) := diamondboxlemma_compr hhc _
    have hAih' : imPred a ≼ (boxPull h (diaPush b (sOne B))).1 := by
      rw [← diaPush_one_val a]; exact hAih
    have hlhs : diaPush d (sOne (comprObj (orth (c ≫ truth C₃')))) =
        diaPush (quotMap (imPred a)) (boxPull h (diaPush b (sOne B))) := by
      rw [← hg'one, ← diaPush_comp, hd, diaPush_comp, hb'one]
    have hrhs : boxPull (pureDagger (quotMap (imPred a))
        (isPure_of_isQuotient (isQuotient_quotMap _)) ≫ h ≫ quotMap (imPred b))
        (sZero (quotObj (imPred b))) =
        diaPush (quotMap (imPred a)) (boxPull h (diaPush b (sOne B))) := by
      rw [boxPull_comp, boxPull_comp, hKb]
      exact boxPull_pureDagger_quot hAi (isQuotient_quotMap (imPred a)) _ hAih'
    rw [hlhs, hrhs]
  · -- ### exactness at `cok b`
    rw [exactAt_iff']
    have hbz : diaPush (quotMap (imPred b)) (diaPush b (sOne B)) =
        sZero (quotObj (imPred b)) := by
      rw [← hKb]
      exact spred_eq_zero (diaPush_boxPull_le (quotMap (imPred b)) _)
    have hlhs : diaPush (pureDagger (quotMap (imPred a))
        (isPure_of_isQuotient (isQuotient_quotMap _)) ≫ h ≫ quotMap (imPred b))
        (sOne (quotObj (imPred a))) =
        diaPush (quotMap (imPred b)) (diaPush h (sOne A')) := by
      rw [diaPush_comp, diaPush_comp, diaPush_pureDagger]
      have e : diaPull (quotMap (imPred a)) (sOne (quotObj (imPred a))) =
          (diaPush a (sOne A)).orth := by
        apply Subtype.ext
        rw [diaPull_one_val, quotient_basics_5 (isQuotient_quotMap (imPred a)),
          ceil_of_isSharp (DiamondEffectus.orth_sharp hAi)]
        change orth (imPred a) = orth (diaPush a (sOne A)).1
        rw [diaPush_one_val]
      rw [e]
      have S2 := order_adj_basics_2 (quotMap (imPred b))
        (order_adj_basics_2 h (spred_isSup_orth_one (diaPush a (sOne A))))
      have hz : (diaPush (quotMap (imPred b))
          (diaPush h (diaPush a (sOne A)))).1 = 0 := by
        refine eq_zero_of_le_zero ?_
        have hx := order_adj_basics_1 (quotMap (imPred b)) hab
        rw [hbz] at hx
        exact hx
      exact (spred_isSup_eq_right S2 hz).symm
    have hkc : diaPush k (diaPush b (sOne B)) = diaPush c (sOne C₃) := by
      rw [← diaPush_comp, ← w₂, diaPush_comp, diaPush_one_of_isQuotient hgq]
    have hbk : imPred b ≼ (boxPull k (diaPush k (diaPush b (sOne B)))).1 := by
      have hx := le_boxPull_diaPush k (diaPush b (sOne B))
      rwa [diaPush_one_val] at hx
    have hrhs : boxPull (pureDagger (quotMap (imPred b))
        (isPure_of_isQuotient (isQuotient_quotMap _)) ≫ k ≫ quotMap (imPred c))
        (sZero (quotObj (imPred c))) =
        diaPush (quotMap (imPred b))
          (boxPull k (diaPush k (diaPush b (sOne B)))) := by
      rw [boxPull_comp, boxPull_comp, hKc, ← hkc]
      exact boxPull_pureDagger_quot hBi (isQuotient_quotMap (imPred b)) _ hbk
    rw [hlhs, hrhs]
    exact (spred_isSup_eq_left (order_adj_basics_2 (quotMap (imPred b)) M3)
      (congrArg Subtype.val hbz)).symm

end Snake

/-! ## The hom-PCM of a finPAC is unique (infrastructure, not a thesis point)

Nothing in this section belongs to parsec 224–228; it is placed here — the
last module of `B/Eff` that does *not* import thesis A — because it is what
`VNExamples.lean` needs and because putting it in `Effectus.lean`, where it
belongs, would invalidate the whole `B/Eff` olean chain.  **Move it to
`Effectus.lean` (next to `FinPAC`) at the next convenient full rebuild.**

The point.  Nine of the eleven von-Neumann examples are stated for an
*arbitrary* `s : EffectusPartialStructure vNᵒᵖ` and must produce their
structure for that `s`, so they were recorded as waiting on a uniqueness
lemma for `EffectusPartialStructure`.  Here is that lemma for the part that
matters: **the PCM-enrichment of a finPAC is not extra data at all** — it is
determined by the category together with its finite coproducts.  Three
steps, each using only the finPAC axioms:

1. `𝟙` on the initial object is `0` (both are maps `0 ⟶ 0`, and `0` is
   initial), so `f = f ≫ 𝟙 = f ≫ 0 = 0` for every `f : X ⟶ 0`: the hom-set
   `C(X, 0)` is a singleton.  Hence `0 = 0_{X,0} ≫ !` is the same morphism
   for any two enrichments (`finPAC_pcm_unique`, first step).
2. With `0` fixed the partial projections `▷₁, ▷₂ : Y + Y ⟶ Y` are fixed,
   and `f ⊥ g` iff `f` and `g` are the two components of a single
   `b : X ⟶ Y + Y` (`perp_iff_exists_bound`): `⇐` is *compatible sum*, and
   `⇒` takes `b = κ₁∘f ⋁ κ₂∘g`, which exists by *untying*.
3. `f ⋁ g = ∇ ∘ b` for any such `b` (`ovee_eq_bound`), since
   `▷₁ ⋁ ▷₂ = ∇` (`ovee_pproj`) and `⋁` commutes with precomposition.

What is **not** determined is the effect object `I` of
`EffectusPartialForm` and its truth map, which are unique only up to
isomorphism — see `docs/BEff-survey.md`. -/

section FinPACUnique

universe u₂

/-- Two `PCM` structures on the same carrier agree as soon as their zero,
their orthogonality relation and their partial sum do. -/
theorem pcm_eq_of_data {M : Type u₂} (p q : PCM M) (hz : p.toZero = q.toZero)
    (hperp : p.Perp = q.Perp)
    (hovee : ∀ (a b : M) (h : p.Perp a b) (h' : q.Perp a b),
      p.ovee a b h = q.ovee a b h') : p = q := by
  cases p with | mk P₁ o₁ _ _ _ _ _ _ _ =>
  cases q with | mk P₂ o₂ _ _ _ _ _ _ _ =>
  simp only at hz hperp hovee
  subst hz
  subst hperp
  congr 1
  funext a b h
  exact hovee a b h h

section OneEnrichment

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D]

/-- Every map into the initial object of a finPAC is `0`.  (`Quotients.lean`
has the same statement for an effectus in *partial form*, deriving it from
`eq_zero_of_one_zero`; the finPAC axioms alone already suffice, which is what
the uniqueness argument needs.) -/
theorem finPAC_eq_zero_of_hom_to_initial {X : D} (f : X ⟶ (⊥_ D)) : f = 0 := by
  have h1 : (𝟙 (⊥_ D)) = (0 : (⊥_ D) ⟶ (⊥_ D)) := initialIsInitial.hom_ext _ _
  calc f = f ≫ 𝟙 (⊥_ D) := by simp
    _ = f ≫ (0 : (⊥_ D) ⟶ (⊥_ D)) := by rw [h1]
    _ = 0 := FinPAC.comp_zero f

/-- The two partial projections `Y + Y ⟶ Y` are orthogonal (compatible sum
at `b = 𝟙`). -/
theorem perp_pproj (Y : D) : Perp (pproj₁ Y Y) (pproj₂ Y Y) := by
  have := FinPAC.compatible_sum (𝟙 (Y ⨿ Y))
  simpa using this

/-- `▷₁ ⋁ ▷₂ = ∇`. -/
theorem ovee_pproj (Y : D) :
    ovee (pproj₁ Y Y) (pproj₂ Y Y) (perp_pproj Y) = coprod.desc (𝟙 Y) (𝟙 Y) := by
  refine coprod.hom_ext ?_ ?_
  · obtain ⟨h', he⟩ := FinPAC.ovee_comp (perp_pproj Y) (coprod.inl : Y ⟶ Y ⨿ Y)
    rw [he]
    simp only [pproj₁, pproj₂, coprod.inl_desc]
    rw [PCM.ovee_zero]
  · obtain ⟨h', he⟩ := FinPAC.ovee_comp (perp_pproj Y) (coprod.inr : Y ⟶ Y ⨿ Y)
    rw [he]
    simp only [pproj₁, pproj₂, coprod.inr_desc]
    rw [PCM.zero_ovee]

/-- `f ⊥ g` exactly when `f` and `g` are the two components of a single
`b : X ⟶ Y + Y`. -/
theorem perp_iff_exists_bound {X Y : D} (f g : X ⟶ Y) :
    Perp f g ↔ ∃ b : X ⟶ Y ⨿ Y, b ≫ pproj₁ Y Y = f ∧ b ≫ pproj₂ Y Y = g := by
  constructor
  · intro h
    refine ⟨ovee (f ≫ (coprod.inl : Y ⟶ Y ⨿ Y)) (g ≫ coprod.inr)
      (FinPAC.untying h), ?_, ?_⟩
    · obtain ⟨h', he⟩ := FinPAC.comp_ovee (FinPAC.untying h) (pproj₁ Y Y)
      rw [he]
      simp only [pproj₁, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        Category.comp_id]
      simp only [FinPAC.comp_zero]
      exact PCM.ovee_zero f _
    · obtain ⟨h', he⟩ := FinPAC.comp_ovee (FinPAC.untying h) (pproj₂ Y Y)
      rw [he]
      simp only [pproj₂, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        Category.comp_id]
      simp only [FinPAC.comp_zero]
      exact PCM.zero_ovee g
  · rintro ⟨b, rfl, rfl⟩
    exact FinPAC.compatible_sum b

/-- The partial sum is computed from any bound: `f ⋁ g = ∇ ∘ b`. -/
theorem ovee_eq_bound {X Y : D} {f g : X ⟶ Y} (h : Perp f g) (b : X ⟶ Y ⨿ Y)
    (h1 : b ≫ pproj₁ Y Y = f) (h2 : b ≫ pproj₂ Y Y = g) :
    ovee f g h = b ≫ coprod.desc (𝟙 Y) (𝟙 Y) := by
  obtain ⟨h', he⟩ := FinPAC.ovee_comp (perp_pproj Y) b
  rw [← ovee_pproj Y, he]
  subst h1; subst h2
  rfl

end OneEnrichment

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]

/-- **The hom-PCM of a finPAC is unique**: any two PCM-enrichments of a
category with finite coproducts satisfying the finPAC axioms are equal. -/
theorem finPAC_pcm_unique (P₁ P₂ : ∀ X Y : D, PCM (X ⟶ Y))
    (h₁ : @FinPAC D _ _ P₁) (h₂ : @FinPAC D _ _ P₂) : P₁ = P₂ := by
  have hz : ∀ X Y : D,
      @Zero.zero _ (P₁ X Y).toZero = @Zero.zero _ (P₂ X Y).toZero := by
    intro X Y
    have e1 : @Zero.zero _ (P₁ X Y).toZero
        = @Zero.zero _ (P₁ X (⊥_ D)).toZero ≫ initial.to Y :=
      (@FinPAC.zero_comp D _ _ P₁ h₁ X (⊥_ D) Y (initial.to Y)).symm
    have e2 : @Zero.zero _ (P₂ X Y).toZero
        = @Zero.zero _ (P₂ X (⊥_ D)).toZero ≫ initial.to Y :=
      (@FinPAC.zero_comp D _ _ P₂ h₂ X (⊥_ D) Y (initial.to Y)).symm
    have e3 : @Zero.zero _ (P₁ X (⊥_ D)).toZero
        = @Zero.zero _ (P₂ X (⊥_ D)).toZero :=
      @finPAC_eq_zero_of_hom_to_initial D _ _ P₂ h₂ X
        (@Zero.zero _ (P₁ X (⊥_ D)).toZero)
    rw [e1, e2, e3]
  have hzero : ∀ X Y : D, (P₁ X Y).toZero = (P₂ X Y).toZero := fun X Y => by
    cases h : (P₁ X Y).toZero; cases h' : (P₂ X Y).toZero
    have hxy := hz X Y
    rw [h, h'] at hxy
    exact congrArg Zero.mk hxy
  have hpp1 : ∀ X Y : D, @pproj₁ D _ _ P₁ X Y = @pproj₁ D _ _ P₂ X Y := by
    intro X Y; simp only [pproj₁]; congr 1; exact hz Y X
  have hpp2 : ∀ X Y : D, @pproj₂ D _ _ P₁ X Y = @pproj₂ D _ _ P₂ X Y := by
    intro X Y; simp only [pproj₂]; congr 1; exact hz X Y
  funext X Y
  refine pcm_eq_of_data _ _ (hzero X Y) ?_ ?_
  · funext f g
    have b1 := @perp_iff_exists_bound D _ _ P₁ h₁ X Y f g
    have b2 := @perp_iff_exists_bound D _ _ P₂ h₂ X Y f g
    rw [hpp1, hpp2] at b1
    exact propext (b1.trans b2.symm)
  · intro f g hf hg
    obtain ⟨b, hb1, hb2⟩ := (@perp_iff_exists_bound D _ _ P₁ h₁ X Y f g).mp hf
    rw [@ovee_eq_bound D _ _ P₁ h₁ X Y f g hf b hb1 hb2]
    rw [hpp1] at hb1
    rw [hpp2] at hb2
    rw [@ovee_eq_bound D _ _ P₂ h₂ X Y f g hg b hb1 hb2]

/-- Consequence for the nine hypothetical von Neumann examples: the
PCM-enrichment carried by an arbitrary `EffectusPartialStructure` is the
canonical one, so a proof may compute with the concrete `⋁` of the intended
structure.  (`HasFiniteCoproducts` is a `Prop`, hence a subsingleton, so the
two structures' coproducts agree on the nose.) -/
theorem effectusPartialStructure_homPCM_unique
    (s s' : EffectusPartialStructure D) : s.homPCM = s'.homPCM := by
  have hc : s'.hasFiniteCoproducts = s.hasFiniteCoproducts := Subsingleton.elim _ _
  have h2 : @FinPAC D _ s.hasFiniteCoproducts s'.homPCM := hc ▸ s'.finPAC
  exact @finPAC_pcm_unique D _ s.hasFiniteCoproducts s.homPCM s'.homPCM s.finPAC h2

end FinPACUnique

end Theses.B.Eff
