import Papers.EJA.Pure
import Theses.B.Eff.Dagger

/-!
# EJA 40: `EJA_psuᵒᵖ` is an `&`-effectus and a †-effectus

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex` (Theorem 40,
main.tex:916).  Over the tree's (finite-dimensional) Euclidean Jordan algebras;
see `Papers/EJA/PLAN.md` §0, §6.

The statement lives in the tree's abstract effectus language
(`Theses/B/Eff/DiamondAmp.lean`, `Theses/B/Eff/Dagger.lean`), at the
partial-form structure `ejapsuPartialStructure` of `EJA_psuᵒᵖ` under which the
tree proves 206III (`diamond_effectus_eja`: `EJA_psuᵒᵖ` is a ⋄-effectus).

Contents.
* **The dictionary** between the tree's effectus notions at `EJA_psuᵒᵖ` and the
  paper's (algebra-direction) notions of `FilterCorner.lean`/`Pure.lean`: a
  quotient for `p` is a filter for `1 - p` (`isQuotient_iff_isFilter`), a
  comprehension for `p` is a corner for `p` (`isComprehension_iff_isCorner`),
  so the two notions of purity agree (`isPure_iff`); `⌈p⌉` is `⌈p⌉`
  (`ejapsuVal_ceilPred`), and the effectus's ⋄-self-adjointness is the paper's
  (`diamondSelfAdjoint_iff`).
* **211II** for `EJA_psuᵒᵖ` (`ejapsu_andThenEffectus`): `asrt_p = Q_{√p}`
  exists (it is pure, and `Q_{√p} = Q_{p^{1/4}} ∘ Q_{p^{1/4}}` with `Q_{p^{1/4}}`
  ⋄-self-adjoint, EJA 33); `π ∘ ξ` is pure (pure maps compose, EJA 31); and
  `asrt_p` is unique **given EJA 34 for ⋄-positivity read literally**
  (`Eja34Literal`, below).
* **215III** for `EJA_psuᵒᵖ` (`ejapsu_daggerPrimeEffectus`): unique square
  roots of predicates, `asrt²_{p&q} = asrt_p asrt²_q asrt_p` (the fundamental
  formula `ejaU_ejaU`), and quotients of sharp predicates are sharp maps.
* **EJA 40** (`eja40`, `eja40_of_pureRoot`).

**The hypothesis.**  The effectus's ⋄-positivity (eff.tex 206II.4, and the
paper's Def 32) asks `f = g ∘ g` for a ⋄-self-adjoint `g` that need **not** be
pure; the paper's proof of 40 cites EJA 34, whose proof uses that `g` is pure
(ERRATA EJA 34; the tree's B15 for `vNᵒᵖ`).  The uniqueness clause of 211II.1
therefore needs EJA 34 without that purity, which is recorded here as the
named hypothesis `Eja34Literal` of the final theorem — exactly as the tree's
`su_andThenEffectus_of_pure_sqrt` took the corresponding hypothesis for
`vNᵒᵖ` before B15 was proved.  `eja34Literal_of_pureRoot` derives it from the
statement "a ⋄-self-adjoint root of a pure map may be replaced by a pure one"
(`PureRootHyp`, the form of the tree's hypothesis), via EJA 34 with the root
pure (`super_duper_theorem`).  Everything else is proved.
-/

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra CategoryTheory Opposite

universe u

set_option warn.classDefReducibility false

attribute [local instance] ejapsuHasFiniteCoproducts ejapsuPCM ejapsuFinPAC
  ejapsuEffectusPartialForm ejapsu_diamondEffectus

/-! ## Elementary facts about `√a` and `Q_{√a}` -/

section Elementary

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- `√a ≤ 1` for an effect `a` (spectrally: `λ² ≤ 1`, `λ ≥ 0` give `λ ≤ 1`). -/
theorem ejaSqrt_le_one {a : V} (h0 : 0 ≤ a) (h1 : a ≤ 1) : ejaSqrt a ≤ 1 := by
  classical
  obtain ⟨hb0, hbb⟩ := ejaSqrt_spec h0
  obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral (ejaSqrt a)
  have hsq : ejaSqrt a * ejaSqrt a = ∑ l ∈ s, (l * l) • e l := by
    rw [hdec]; exact eja_ortho_mul hidem horth (fun l => l) (fun l => l)
  have hnn : ∀ l ∈ s, 0 ≤ l := by
    have h := (eja_nonneg_iff _).mp hb0
    rw [hdec] at h
    exact (eja_ortho_isSumSq_iff hidem horth hne0 (fun l => l)).mp h
  have hsq1 : ∀ l ∈ s, 0 ≤ l * l ∧ l * l ≤ 1 := by
    refine (eja_ortho_unit_interval_iff hidem horth hne0 hsum (fun l => l * l)).mp ?_
    rw [← hsq, hbb]; exact ⟨h0, h1⟩
  have h := (eja_ortho_unit_interval_iff hidem horth hne0 hsum (fun l => l)).mpr
    (fun l hl => ⟨hnn l hl, by nlinarith [hnn l hl, (hsq1 l hl).2]⟩)
  rw [hdec]; exact h.2

/-- `Q_{√b} b = b²`. -/
theorem ejaU_sqrt_self {b : V} (hb : 0 ≤ b) : ejaU (ejaSqrt b) b = b * b := by
  obtain ⟨_, hss⟩ := ejaSqrt_spec hb
  have h : ejaU (ejaSqrt b) b = ejaU (ejaSqrt b) (ejaU (ejaSqrt b) 1) := by
    rw [ejaU_apply_one, hss]
  rw [h, ← ejaU_mul_self, hss, ejaU_apply_one]

/-- `Q_{√a} ∘ Q_{√a} = Q_a`. -/
theorem ejaU_sqrt_sqrt {a : V} (ha : 0 ≤ a) (y : V) :
    ejaU (ejaSqrt a) (ejaU (ejaSqrt a) y) = ejaU a y := by
  rw [← ejaU_mul_self, (ejaSqrt_spec ha).2]

/-- `Q_{√a} ∘ Q_{⌈a⌉} = Q_{√a}` for an effect `a` (the fundamental formula at
`(⌈a⌉, √a)`, with `Q_{⌈a⌉} √a = √a`). -/
theorem ejaU_sqrt_pone_ceil {a : V} (h0 : 0 ≤ a) (h1 : a ≤ 1) (x : V) :
    ejaU (ejaSqrt a) (ejaPone (ejaCeil a) x) = ejaU (ejaSqrt a) x := by
  have hs := ejaCeil_idem a
  have hvw := ceil_mul_sqrt h0 h1
  have hsw : ejaU (ejaCeil a) (ejaSqrt a) = ejaSqrt a := by
    rw [ejaU_idem hs]; exact (eja_pone_eq_self_iff _ hs _).mpr hvw
  have hFF := ejaU_ejaU (ejaCeil a) (ejaSqrt a)
  rw [hsw] at hFF
  have hss : ejaU (ejaCeil a) (ejaU (ejaCeil a) x) = ejaU (ejaCeil a) x := by
    rw [← Module.End.mul_apply, idem_Q_idem hs]
  rw [← ejaU_idem hs, hFF]
  simp only [Module.End.mul_apply]
  rw [hss]

end Elementary

/-- `Q_b` (for `b² ≤ 1`) as an endomorphism of `EJA_psu`. -/
def uHom (E : EJAPsu.{u}) (b : E.carrier) (hb : b * b ≤ 1) : E ⟶ E where
  toLinearMap := ejaU b
  map_nonneg' _ hx := eja_U_nonneg' b hx
  map_subunital' := by rw [ejaU_apply_one]; exact hb

@[simp] theorem uHom_apply (E : EJAPsu.{u}) (b : E.carrier) (hb : b * b ≤ 1) (x : E.carrier) :
    (uHom E b hb).toLinearMap x = ejaU b x := rfl

/-! ## Pure maps: filters, corners and `Q_{√a}` -/

section PureMaps

/-- The identity is a filter for `1`. -/
theorem isFilter_one_id (E : EJAPsu.{u}) : IsFilter (1 : E.carrier) (𝟙 E) :=
  ⟨le_refl _, fun _ f _ => ⟨f, Category.comp_id f, fun k hk =>
    (Category.comp_id k).symm.trans hk⟩⟩

theorem ejapsu_one_nonneg' (E : EJAPsu.{u}) : (0 : E.carrier) ≤ 1 :=
  (eja_nonneg_iff _).mpr eja_isSumSq_one

/-- A filter is pure (its corner is the identity, a corner for `1`). -/
theorem isPure_of_isFilter {E D : EJAPsu.{u}} {q : E.carrier} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {ξ : D ⟶ E} (h : IsFilter q ξ) : Papers.EJA.IsPure ξ :=
  ⟨D, 1, q, 𝟙 D, ξ, ⟨ejapsu_one_nonneg' D, le_refl _⟩, ⟨hq0, hq1⟩,
    isCorner_one_of_iso (Category.id_comp _) (Category.id_comp _), h,
    (Category.id_comp ξ).symm⟩

/-- A corner is pure (its filter is the identity, a filter for `1`). -/
theorem isPure_of_isCorner {E C : EJAPsu.{u}} {b : E.carrier} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {π : E ⟶ C} (h : IsCorner b π) : Papers.EJA.IsPure π :=
  ⟨C, b, 1, π, 𝟙 C, ⟨hb0, hb1⟩, ⟨ejapsu_one_nonneg' C, le_refl _⟩, h, isFilter_one_id C,
    (Category.comp_id π).symm⟩

/-- `Q_{√a}` is pure: it is the standard filter `ξ_a` after the standard corner
`π_{⌈a⌉}` (main.tex, text after EJA 25), by the fundamental formula
(`ejaU_sqrt_pone_ceil`). -/
theorem isPure_uHom_sqrt (E : EJAPsu.{u}) {a : E.carrier} (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (hb : ejaSqrt a * ejaSqrt a ≤ 1) : Papers.EJA.IsPure (uHom E (ejaSqrt a) hb) := by
  have hc := ejaCeil_idem a
  have hfc : (floorIdem (ejaCeil a)).elt = (ceilIdem a).elt := ejaFloor_idem_eq hc
  have hc0 : 0 ≤ ejaCeil a := eja_idem_nonneg hc
  have hc1 : ejaCeil a ≤ 1 := eja_idem_le_one hc
  refine ⟨filterObj E a, ejaCeil a, a, stdCorner E (ejaCeil a) ≫ cornerCast E _ _ hfc,
    stdFilter E h0 h1, ⟨hc0, hc1⟩, ⟨h0, h1⟩,
    (stdCorner_isCorner E hc0 hc1).comp_iso (cornerCast_comp E _ _ hfc)
      (cornerCast_comp E _ _ hfc.symm),
    (stdFilter_isFilter E h0 h1).2, ?_⟩
  refine ejapsu_hom_ext fun x => ?_
  show ejaU (ejaSqrt a) x = ejaU (ejaSqrt a) (EJACorner.val
    ((cornerCast E _ _ hfc).toLinearMap ((stdCorner E (ejaCeil a)).toLinearMap x)))
  rw [cornerCast_val, stdCorner_val, ejaFloor_idem_eq hc, ejaU_sqrt_pone_ceil h0 h1]

/-- A filter for an idempotent maps idempotents to idempotents (main.tex, proof
of EJA 40, item 3): the standard filter of an idempotent is an inclusion, and
every filter is the standard one after an isomorphism (EJA 36). -/
theorem IsFilter.map_idem {E D : EJAPsu.{u}} {e : E.carrier} (he : e * e = e) {ξ : D ⟶ E}
    (h : IsFilter e ξ) {t : D.carrier} (ht : t * t = t) :
    ξ.toLinearMap t * ξ.toLinearMap t = ξ.toLinearMap t := by
  have he0 := eja_idem_nonneg he
  have he1 := eja_idem_le_one he
  obtain ⟨θ, θ', hθσ, hθθ', hθ'θ⟩ := filter_iso h (stdFilter_isFilter E he0 he1).2
  have hsq : ejaSqrt e = e := ejaSqrt_unique he0 he
  have hce : ejaCeil e = e := ejaCeil_idem_eq he
  have hval : ∀ y : (filterObj E e).carrier,
      (stdFilter E he0 he1).toLinearMap y = EJACorner.val y := by
    intro y
    have hv : ejaCeil e * EJACorner.val y = EJACorner.val y := EJACorner.val_prop y
    rw [hce] at hv
    rw [stdFilter_apply, hsq, ejaU_idem he]
    exact (eja_pone_eq_self_iff _ he _).mpr hv
  have hθt : θ.toLinearMap t * θ.toLinearMap t = θ.toLinearMap t := by
    rw [← ejapsu_iso_mul hθθ' hθ'θ, ht]
  rw [← hθσ, ejapsu_comp_apply, hval, ← EJACorner.val_mul, hθt]

end PureMaps

/-! ## The dictionary: effectus notions at `EJA_psuᵒᵖ` versus the paper's -/

section Dictionary

theorem one_sub_le_one {E : EJAPsu.{u}} {a : E.carrier} (h : 0 ≤ a) : 1 - a ≤ 1 := by
  rw [eja_le_iff, sub_sub_cancel]; exact (eja_nonneg_iff _).mp h

/-- **197II at `EJA_psuᵒᵖ`**: a quotient for the predicate `p` is exactly a
filter (EJA 16) for the effect `1 - p`. -/
theorem isQuotient_iff_isFilter {X Q : EJAPsu.{u}ᵒᵖ} (p : Pred X) (ξ : X ⟶ Q) :
    IsQuotient p ξ ↔ IsFilter (1 - ejapsuVal p) ξ.unop := by
  have hle : ∀ {Y : EJAPsu.{u}ᵒᵖ} (f : X ⟶ Y),
      (f ≫ truth Y) ≼ orth p ↔ f.unop.toLinearMap 1 ≤ 1 - ejapsuVal p := by
    intro Y f
    rw [ejapsuVal_le_iff, ejapsuVal_comp, ejapsuVal_truth, ejapsuVal_orth]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hle ξ).mp h1, fun F f hf => ?_⟩
    obtain ⟨f', hf', hu⟩ := h2 f.op ((hle f.op).mpr hf)
    refine ⟨f'.unop, congrArg Quiver.Hom.unop hf', fun k hk => ?_⟩
    have := hu k.op (Quiver.Hom.unop_inj hk)
    rw [← this]; rfl
  · rintro ⟨h1, h2⟩
    refine ⟨(hle ξ).mpr h1, fun Y f hf => ?_⟩
    obtain ⟨fb, hfb, hu⟩ := h2 Y.unop f.unop ((hle f).mp hf)
    refine ⟨fb.op, Quiver.Hom.unop_inj hfb, fun k hk => ?_⟩
    have := hu k.unop (congrArg Quiver.Hom.unop hk)
    rw [← this]; rfl

/-- **199II at `EJA_psuᵒᵖ`**: a comprehension for the predicate `p` is exactly
a corner (EJA 14) for the effect `p`. -/
theorem isComprehension_iff_isCorner {W X : EJAPsu.{u}ᵒᵖ} (p : Pred X) (π : W ⟶ X) :
    IsComprehension p π ↔ IsCorner (ejapsuVal p) π.unop := by
  have heq : ∀ {Z : EJAPsu.{u}ᵒᵖ} (g : Z ⟶ X),
      g ≫ p = g ≫ truth X ↔ g.unop.toLinearMap 1 = g.unop.toLinearMap (ejapsuVal p) := by
    intro Z g
    constructor
    · intro h
      have h2 := congrArg ejapsuVal h
      rw [ejapsuVal_comp, ejapsuVal_comp, ejapsuVal_truth] at h2
      exact h2.symm
    · intro h
      refine ejapsuVal_injective ?_
      rw [ejapsuVal_comp, ejapsuVal_comp, ejapsuVal_truth]
      exact h.symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(heq π).mp h1, fun F g hg => ?_⟩
    obtain ⟨g', hg', hu⟩ := h2 g.op ((heq g.op).mpr hg)
    refine ⟨g'.unop, congrArg Quiver.Hom.unop hg', fun k hk => ?_⟩
    have := hu k.op (Quiver.Hom.unop_inj hk)
    rw [← this]; rfl
  · rintro ⟨h1, h2⟩
    refine ⟨(heq π).mpr h1, fun Z g hg => ?_⟩
    obtain ⟨gb, hgb, hu⟩ := h2 Z.unop g.unop ((heq g).mp hg)
    refine ⟨gb.op, Quiver.Hom.unop_inj hgb, fun k hk => ?_⟩
    have := hu k.unop (congrArg Quiver.Hom.unop hk)
    rw [← this]; rfl

/-- **201II at `EJA_psuᵒᵖ`**: the effectus's purity (a comprehension after a
quotient) is the paper's (EJA 18: a filter after a corner, in the algebra
direction). -/
theorem isPure_iff {X Y : EJAPsu.{u}ᵒᵖ} (f : X ⟶ Y) :
    Theses.B.Eff.IsPure f ↔ Papers.EJA.IsPure f.unop := by
  constructor
  · rintro ⟨Q, ξ, π, p, q, hξ, hπ, rfl⟩
    exact ⟨Q.unop, ejapsuVal q, 1 - ejapsuVal p, π.unop, ξ.unop,
      ⟨ejapsuVal_nonneg q, ejapsuVal_le_one q⟩,
      ⟨eja_sub_nonneg.mpr (ejapsuVal_le_one p), one_sub_le_one (ejapsuVal_nonneg p)⟩,
      (isComprehension_iff_isCorner q π).mp hπ, (isQuotient_iff_isFilter p ξ).mp hξ, rfl⟩
  · rintro ⟨C, q, q', π, ξ, ⟨hq0, hq1⟩, ⟨hq'0, hq'1⟩, hπ, hξ, hf⟩
    have hp0 : (0 : X.unop.carrier) ≤ 1 - q' := eja_sub_nonneg.mpr hq'1
    have hp1 : (1 : X.unop.carrier) - q' ≤ 1 := one_sub_le_one hq'0
    refine ⟨op C, ξ.op, π.op, ejapsuPredOf X hp0 hp1, ejapsuPredOf Y hq0 hq1, ?_, ?_,
      Quiver.Hom.unop_inj hf⟩
    · refine (isQuotient_iff_isFilter _ _).mpr ?_
      rw [ejapsuVal_predOf, sub_sub_cancel]
      exact hξ
    · refine (isComprehension_iff_isCorner _ _).mpr ?_
      rw [ejapsuVal_predOf]
      exact hπ

/-- **203I at `EJA_psuᵒᵖ`**: the effectus's ceiling `⌈p⌉` is the least
idempotent above the effect (EJA 13). -/
theorem ejapsuVal_ceilPred {X : EJAPsu.{u}ᵒᵖ} (p : Pred X) :
    ejapsuVal (ceilPred p) = ejaCeil (ejapsuVal p) := by
  have h0 := ejapsuVal_nonneg p
  have h1 := ejapsuVal_le_one p
  obtain ⟨hcid, hle, hmin⟩ := (EJAceilfloor h0 h1).2.2.1
  have hcs : ejapsuVal (ceilPred p) * ejapsuVal (ceilPred p) = ejapsuVal (ceilPred p) :=
    (ejapsu_isSharp_iff _).mp (isSharp_ceil p)
  refine le_antisymm ?_ (hmin _ hcs ((ejapsuVal_le_iff _ _).mp (le_ceil p)))
  have hq : ejapsuVal (ejapsuPredOf X (eja_idem_nonneg hcid) (eja_idem_le_one hcid))
      = ejaCeil (ejapsuVal p) := ejapsuVal_predOf _ _ _
  have hsq : IsSharp (ejapsuPredOf X (eja_idem_nonneg hcid) (eja_idem_le_one hcid)) :=
    (ejapsu_isSharp_iff _).mpr (by rw [hq]; exact hcid)
  have h := (ejapsuVal_le_iff _ _).mp ((ceil_le_iff_of_isSharp (p := p) hsq).mpr
    ((ejapsuVal_le_iff _ _).mpr (by rw [hq]; exact hle)))
  rwa [hq] at h

/-- `f^⋄(s) ≤ tᗮ ⟺ t * f(s) = 0` for sharp `s, t` (EJA 32 against 206II). -/
theorem diaPull_le_orth_iff {X Y : EJAPsu.{u}ᵒᵖ} (f : X ⟶ Y) (s : SPred Y) (t : SPred X) :
    (diaPull f s).1 ≼ orth t.1 ↔
      ejapsuVal t.1 * f.unop.toLinearMap (ejapsuVal s.1) = 0 := by
  rw [ejapsuVal_le_iff, ejapsuVal_orth]
  show ejapsuVal (ceilPred (f ≫ s.1)) ≤ _ ↔ _
  rw [ejapsuVal_ceilPred, ejapsuVal_comp]
  exact diaUp_le_iff (f := f.unop.toLinearMap) f.unop.map_nonneg' f.unop.map_subunital'
    ((ejapsu_isSharp_iff _).mp s.2) ((ejapsu_isSharp_iff _).mp t.2)

/-- The sharp predicate with a given idempotent as its value. -/
def spredOf (X : EJAPsu.{u}ᵒᵖ) {s : X.unop.carrier} (hs : s * s = s) : SPred X :=
  ⟨ejapsuPredOf X (eja_idem_nonneg hs) (eja_idem_le_one hs),
    (ejapsu_isSharp_iff _).mpr (by rw [ejapsuVal_predOf]; exact hs)⟩

@[simp] theorem ejapsuVal_spredOf (X : EJAPsu.{u}ᵒᵖ) {s : X.unop.carrier} (hs : s * s = s) :
    ejapsuVal (spredOf X hs).1 = s := ejapsuVal_predOf _ _ _

/-- Effectus-⋄-self-adjointness (206II.2) gives the paper's (EJA 32). -/
theorem isDiaSA_of_diamondSelfAdjoint {X : EJAPsu.{u}ᵒᵖ} {g : X ⟶ X}
    (hg : DiamondSelfAdjoint g) : IsDiaSA g.unop.toLinearMap := by
  rw [diaSA_iff g.unop.map_nonneg' g.unop.map_subunital']
  intro s hs t ht
  have h := diamond_adjunction g (spredOf X hs) (spredOf X ht)
  have hg' : diaPull g = diaPush g := hg
  rw [← hg', diaPull_le_orth_iff, diaPull_le_orth_iff, ejapsuVal_spredOf,
    ejapsuVal_spredOf] at h
  exact h

/-- The paper's ⋄-self-adjointness (EJA 32) gives the effectus's (206II.2): by
**207III** `diamond_adjunction` it suffices that `g^⋄` be symmetric. -/
theorem diamondSelfAdjoint_of_isDiaSA {X : EJAPsu.{u}ᵒᵖ} {g : X ⟶ X}
    (hg : IsDiaSA g.unop.toLinearMap) : DiamondSelfAdjoint g := by
  have hZ := (diaSA_iff g.unop.map_nonneg' g.unop.map_subunital').mp hg
  have hsymm : ∀ s t : SPred X,
      (diaPull g s).1 ≼ orth t.1 ↔ (diaPull g t).1 ≼ orth s.1 := by
    intro s t
    rw [diaPull_le_orth_iff, diaPull_le_orth_iff]
    exact hZ _ ((ejapsu_isSharp_iff _).mp s.2) _ ((ejapsu_isSharp_iff _).mp t.2)
  show diaPull g = diaPush g
  refine funext fun t => Subtype.ext (eabasics_le_antisymm ?_ ?_)
  · have h0 : (diaPush g t).1 ≼ orth ((diaPush g t).orth).1 := by
      rw [spred_orth_val, eabasics_orth_orth]
      exact pcm_preorder_refl _
    have h2 := (hsymm (diaPush g t).orth t).mp
      ((diamond_adjunction g (diaPush g t).orth t).mpr h0)
    rw [spred_orth_val, eabasics_orth_orth] at h2
    exact h2
  · have h0 : (diaPull g t).1 ≼ orth ((diaPull g t).orth).1 := by
      rw [spred_orth_val, eabasics_orth_orth]
      exact pcm_preorder_refl _
    have h2 := (diamond_adjunction g (diaPull g t).orth t).mp
      ((hsymm t (diaPull g t).orth).mp h0)
    rw [spred_orth_val, eabasics_orth_orth] at h2
    exact h2

/-- **206II.2 at `EJA_psuᵒᵖ`**: the effectus's ⋄-self-adjointness is the
paper's (EJA 32). -/
theorem diamondSelfAdjoint_iff {X : EJAPsu.{u}ᵒᵖ} (g : X ⟶ X) :
    DiamondSelfAdjoint g ↔ IsDiaSA g.unop.toLinearMap :=
  ⟨isDiaSA_of_diamondSelfAdjoint, diamondSelfAdjoint_of_isDiaSA⟩

end Dictionary

/-! ## 211II at `EJA_psuᵒᵖ`: existence of `asrt_p`, and `π ∘ ξ` pure -/

section AndThen

/-- **211II.1 at `EJA_psuᵒᵖ`, existence**: `Q_{√p}` is a ⋄-positive map with
`1 ∘ Q_{√p} = p` — pure (`isPure_uHom_sqrt`), and the square of the
⋄-self-adjoint (EJA 33) map `Q_{p^{1/4}}`. -/
theorem ejapsu_exists_asrt {X : EJAPsu.{u}ᵒᵖ} (p : Pred X) :
    ∃ k : X ⟶ X, DiamondPositive k ∧ k ≫ truth X = p ∧
      ∀ x, k.unop.toLinearMap x = ejaU (ejaSqrt (ejapsuVal p)) x := by
  have h0 := ejapsuVal_nonneg p
  have h1 := ejapsuVal_le_one p
  obtain ⟨hb0, hbb⟩ := ejaSqrt_spec h0
  have hb1 := ejaSqrt_le_one h0 h1
  obtain ⟨-, hrr⟩ := ejaSqrt_spec hb0
  have hbsq : ejaSqrt (ejapsuVal p) * ejaSqrt (ejapsuVal p) ≤ 1 := by rw [hbb]; exact h1
  have hrsq : ejaSqrt (ejaSqrt (ejapsuVal p)) * ejaSqrt (ejaSqrt (ejapsuVal p)) ≤ 1 := by
    rw [hrr]; exact hb1
  refine ⟨(uHom X.unop _ hbsq).op, ⟨?_, (uHom X.unop _ hrsq).op, ?_, ?_⟩, ?_, fun x => rfl⟩
  · exact (isPure_iff _).mpr (isPure_uHom_sqrt X.unop h0 h1 hbsq)
  · exact diamondSelfAdjoint_of_isDiaSA (diamond_adjointness_Q _ hrsq)
  · refine Quiver.Hom.unop_inj (ejapsu_hom_ext fun x => ?_)
    show ejaU (ejaSqrt (ejapsuVal p)) x
      = ejaU (ejaSqrt (ejaSqrt (ejapsuVal p))) (ejaU (ejaSqrt (ejaSqrt (ejapsuVal p))) x)
    rw [ejaU_sqrt_sqrt hb0]
  · refine ejapsuVal_injective ?_
    rw [ejapsuVal_comp, ejapsuVal_truth]
    show ejaU (ejaSqrt (ejapsuVal p)) 1 = ejapsuVal p
    rw [ejaU_apply_one, hbb]

/-- **211II.2 at `EJA_psuᵒᵖ`**: a quotient after a comprehension, `π ∘ ξ`, is
pure — in the algebra direction a filter followed by a corner, pure by EJA 31
(`purepure`). -/
theorem ejapsu_quot_after_compr_pure {X Y Z : EJAPsu.{u}ᵒᵖ} {p q : Pred Y}
    (π : X ⟶ Y) (ξ : Y ⟶ Z) (hπ : IsComprehension p π) (hξ : IsQuotient q ξ) :
    Theses.B.Eff.IsPure (π ≫ ξ) := by
  rw [isPure_iff]
  have hc := (isComprehension_iff_isCorner p π).mp hπ
  have hf := (isQuotient_iff_isFilter q ξ).mp hξ
  exact purepure
    (isPure_of_isFilter (eja_sub_nonneg.mpr (ejapsuVal_le_one q))
      (one_sub_le_one (ejapsuVal_nonneg q)) hf)
    (isPure_of_isCorner (ejapsuVal_nonneg p) (ejapsuVal_le_one p) hc)

/-- **EJA 34 with Def 32 read literally**: a pure `g` that is `f ∘ f` for a
⋄-self-adjoint positive subunital `f` — **not** assumed pure — is
`Q_{√g(1)}`.  This is what 211II.1's uniqueness needs; the paper proves 34
only with `f` pure (`super_duper_theorem`; ERRATA EJA 34).  Open; carried as a
hypothesis of `eja40`. -/
def Eja34Literal : Prop :=
  ∀ (E : EJAPsu.{u}) (g f : E ⟶ E), Papers.EJA.IsPure g → IsDiaSA f.toLinearMap →
    g = f ≫ f → ∀ x, g.toLinearMap x = ejaU (ejaSqrt (g.toLinearMap 1)) x

/-- The tree's form of the hypothesis (`su_andThenEffectus_of_pure_sqrt`'s `H`
for `vNᵒᵖ`, B15): a ⋄-self-adjoint `f` whose square is pure has a *pure*
⋄-self-adjoint square root with the same square. -/
def PureRootHyp : Prop :=
  ∀ (E : EJAPsu.{u}) (f : E ⟶ E), IsDiaSA f.toLinearMap → Papers.EJA.IsPure (f ≫ f) →
    ∃ h : E ⟶ E, Papers.EJA.IsPure h ∧ IsDiaSA h.toLinearMap ∧ f ≫ f = h ≫ h

/-- `PureRootHyp` implies `Eja34Literal`, through EJA 34 with the root pure
(`super_duper_theorem`). -/
theorem eja34Literal_of_pureRoot (H : PureRootHyp.{u}) : Eja34Literal.{u} := by
  intro E g f hg hf hgf
  subst hgf
  obtain ⟨h, hh, hhsa, hfh⟩ := H E f hf hg
  rw [hfh]
  exact super_duper_theorem (h ≫ h) (hfh ▸ hg) ⟨h, hh, hhsa, rfl⟩

/-- **EJA 40, first half** (main.tex:916–930, the proof's "`&`-effectus"
step; eff.tex 211II): `EJA_psuᵒᵖ` is an `&`-effectus — given `Eja34Literal`
for the uniqueness of `asrt_p`.  Existence is `ejapsu_exists_asrt`, the second
axiom `ejapsu_quot_after_compr_pure`. -/
theorem ejapsu_andThenEffectus (H : Eja34Literal.{u}) : AndThenEffectus (EJAPsu.{u}ᵒᵖ) :=
  { ejapsu_diamondEffectus with
    existsUnique_asrt := by
      intro X p
      obtain ⟨k, hkpos, hk1, hkval⟩ := ejapsu_exists_asrt p
      refine ⟨k, ⟨hkpos, hk1⟩, ?_⟩
      rintro k' ⟨⟨hk'pure, g, hgsa, hk'g⟩, hk'1⟩
      have ha : k'.unop.toLinearMap 1 = ejapsuVal p := by
        have h2 := congrArg ejapsuVal hk'1
        rwa [ejapsuVal_comp, ejapsuVal_truth] at h2
      have hk' := H X.unop k'.unop g.unop ((isPure_iff k').mp hk'pure)
        (isDiaSA_of_diamondSelfAdjoint hgsa) (congrArg Quiver.Hom.unop hk'g)
      refine Quiver.Hom.unop_inj (ejapsu_hom_ext fun x => ?_)
      rw [hk' x, hkval x, ha]
    quot_after_compr_pure := fun π ξ hπ hξ => ejapsu_quot_after_compr_pure π ξ hπ hξ }

end AndThen

/-! ## 215III at `EJA_psuᵒᵖ` -/

section DaggerPrime

variable [AndThenEffectus (EJAPsu.{u}ᵒᵖ)]

/-- **211IV-style formula at `EJA_psuᵒᵖ`**: `asrt_p = Q_{√p}`, `b ↦ Q_{√p} b`
(main.tex, proof of EJA 40), for any `&`-effectus structure on `EJA_psuᵒᵖ`. -/
theorem ejapsu_asrt_apply {X : EJAPsu.{u}ᵒᵖ} (p : Pred X) (x : X.unop.carrier) :
    (asrt p).unop.toLinearMap x = ejaU (ejaSqrt (ejapsuVal p)) x := by
  obtain ⟨k, hpos, h1, hk⟩ := ejapsu_exists_asrt p
  rw [← asrt_unique p k hpos h1, hk]

/-- `p & q = Q_{√p} q`. -/
theorem ejapsuVal_andThen {X : EJAPsu.{u}ᵒᵖ} (p q : Pred X) :
    ejapsuVal (andThen p q) = ejaU (ejaSqrt (ejapsuVal p)) (ejapsuVal q) := by
  show ejapsuVal (asrt p ≫ q) = _
  rw [ejapsuVal_comp, ejapsu_asrt_apply]

/-- **215III at `EJA_psuᵒᵖ`** (main.tex, proof of EJA 40, items 1–3):
`EJA_psuᵒᵖ` is a †′-effectus.
1. `q & q = q²`, so a predicate's unique square root is `√p` (square roots of
   positive elements are unique, `sqrt_unique`, and `√p ≤ 1`);
2. `asrt²_{p&q} = Q_{Q_{√p} q}` and `asrt_p asrt²_q asrt_p = Q_{√p} Q_q Q_{√p}`:
   the fundamental formula (`ejaU_ejaU`);
3. a quotient for a sharp `s` is a filter for the idempotent `1 - s`, which
   maps idempotents to idempotents (`IsFilter.map_idem`). -/
theorem ejapsu_daggerPrimeEffectus : DaggerPrimeEffectus (EJAPsu.{u}ᵒᵖ) where
  sqrt_existsUnique := by
    intro X p
    have h0 := ejapsuVal_nonneg p
    have h1 := ejapsuVal_le_one p
    obtain ⟨hb0, hbb⟩ := ejaSqrt_spec h0
    have key : ∀ q : Pred X,
        andThen q q = p ↔ ejapsuVal q * ejapsuVal q = ejapsuVal p := by
      intro q
      rw [← ejaU_sqrt_self (ejapsuVal_nonneg q), ← ejapsuVal_andThen]
      exact ⟨congrArg ejapsuVal, fun h => ejapsuVal_injective h⟩
    refine ⟨ejapsuPredOf X hb0 (ejaSqrt_le_one h0 h1),
      (key _).mpr (by rw [ejapsuVal_predOf, hbb]), fun q hq => ?_⟩
    refine ejapsuVal_injective ?_
    rw [ejapsuVal_predOf]
    exact (ejaSqrt_unique (ejapsuVal_nonneg q) ((key q).mp hq)).symm
  asrt_sq := by
    intro X p q
    refine ejapsuop_hom_ext fun x => ?_
    simp only [ejapsuop_comp_apply, ejapsu_asrt_apply, ejapsuVal_andThen]
    rw [ejaU_sqrt_sqrt (eja_U_nonneg' _ (ejapsuVal_nonneg q)),
      ejaU_sqrt_sqrt (ejapsuVal_nonneg q), ejaU_ejaU_apply]
  quot_sharp := by
    intro X W s hs ξ hξ t ht
    rw [ejapsu_isSharp_iff] at hs ht ⊢
    rw [ejapsuVal_comp]
    exact IsFilter.map_idem (eja_one_sub_idem hs) ((isQuotient_iff_isFilter s ξ).mp hξ) ht

end DaggerPrime

/-! ## EJA 40 -/

/-- **EJA 40** (main.tex:916, Theorem): `EJA_psuᵒᵖ` is a †-effectus (as
defined in thesis B §215), with `asrt_p = Q_{√p}` — **given `Eja34Literal`**
(EJA 34 for ⋄-positive maps in the literal sense of Def 32, whose root need not
be pure; the print's proof cites 34, whose own proof assumes the root pure).
The ⋄-effectus part is the tree's `diamond_effectus_eja`; the `&`-effectus
part is `ejapsu_andThenEffectus`; the †-effectus structure comes from 215III's
sufficiency half (`dagger_thm_sufficiency`) applied to the †′-effectus
`ejapsu_daggerPrimeEffectus`. -/
theorem eja40 (H : Eja34Literal.{u}) :
    letI := ejapsu_andThenEffectus H
    (∀ {X : EJAPsu.{u}ᵒᵖ} (p : Pred X) (x : X.unop.carrier),
      (asrt p).unop.toLinearMap x = ejaU (ejaSqrt (ejapsuVal p)) x) ∧
    DaggerPrimeEffectus (EJAPsu.{u}ᵒᵖ) ∧ Nonempty (DaggerEffectus (EJAPsu.{u}ᵒᵖ)) := by
  let _ := ejapsu_andThenEffectus H
  have _ : DaggerPrimeEffectus (EJAPsu.{u}ᵒᵖ) := ejapsu_daggerPrimeEffectus
  exact ⟨fun p x => ejapsu_asrt_apply p x, ejapsu_daggerPrimeEffectus, dagger_thm_sufficiency⟩

/-- **EJA 40** with the hypothesis in the tree's form (`PureRootHyp`, B15 for
`EJA_psuᵒᵖ`): a ⋄-self-adjoint root of a pure map may be taken pure. -/
theorem eja40_of_pureRoot (H : PureRootHyp.{u}) :
    letI := ejapsu_andThenEffectus (eja34Literal_of_pureRoot H)
    Nonempty (DaggerEffectus (EJAPsu.{u}ᵒᵖ)) :=
  (eja40 (eja34Literal_of_pureRoot H)).2.2

end Papers.EJA
