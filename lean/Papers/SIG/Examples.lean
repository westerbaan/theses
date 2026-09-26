/-
Papers/SIG/Examples.lean

SIG 15 (`ex:wstar`, main.tex:548) and SIG 46 (main.tex:1245).

* **SIG 15**: the opposite of the category of W*-algebras is a σ-effectus
  with unit `ℂ`, a family of maps being summable iff the finite partial sums
  of the `f_j(1)` stay below `1`, its sum the ultraweak sum; predicates are
  the effects `[0,1]_𝔄`, total maps the unital maps, states the normal
  states.  Proved twice:
  - as printed, for the category `W*` (`WStarPSU`) of von Neumann algebras
    and normal *positive* subunital maps (`NPSUMap`): `pvnSigmaEffectus`,
    with `pvn_summable_iff`, `pvn_sumsTo_iff`, `pvn_pred_effects`,
    `pvn_isTotal_iff`;
  - for the tree's `W*_cpsu` (`WStarCPSU`, normal *completely* positive
    subunital maps), extending the tree's partial-form effectus
    `vnPartialStructure` (same binary sums, `vn_pcm_eq_suPCM`):
    `vnSigmaEffectus`, with `vn_summable_iff`, `vn_sumsTo_iff`, ….
  New in both: countable coproducts (the ℓ^∞-direct sums `⊕_j 𝒜_j` over the
  non-zero summands; tree **47IV** for cp maps, `pos_products` for positive
  maps), the σ-PAM of ultraweak sums on the hom-sets (pointwise canonical
  sums on the effects, which are a σ-effect algebra; existence from the
  tree's `exists_ncp_uwsum` **96III**, and its positive-map version
  `exists_pos_uwsum`), and the effectus axioms.
* **SIG 46**: `sEA ≅ sEMod[{0,1}]` (an isomorphism of categories, identity
  on carriers and maps, `sig46_iso`), so `sEAᵒᵖ` is a σ-effectus
  (transported with `Convex`'s transport) with scalars `{0,1}`
  (`sea_scalars`); the effects `[0,1]_𝒜` and the projections `P(𝒜)` of a von
  Neumann algebra are σ-effect algebras, `P(𝒜) ⊆ [0,1]_𝒜` a σ-subalgebra; and
  the Kochen–Specker consequence (`sig46_kochenSpecker`), with KS itself as
  the named hypothesis `KochenSpecker`.
-/
import Papers.SIG.Convex
import Papers.SIG.Pfn
import Theses.B.Eff.VNExamples
import Theses.B.Dils.WittrockSplit

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite
open scoped ComplexOrder ENNReal

namespace Papers.SIG

open SigmaPAM

universe u

/-! ## The effects of a von Neumann algebra as a σ-effect algebra -/

section Effects

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Theses.VonNeumannAlgebra A]

/-- The algebraic order of `[0,1]_𝒜` is the order of `𝒜`. -/
theorem eff_le_iff (a b : Theses.effects A) : a ≼ b ↔ (a : A) ≤ b := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    show (a : A) ≤ a + c
    exact le_add_of_nonneg_right c.2.1
  · intro h
    refine ⟨⟨(b : A) - a, sub_nonneg.mpr h, (sub_le_self _ a.2.1).trans b.2.2⟩, ?_, ?_⟩
    · show (a : A) + (b - a) ≤ 1
      rw [add_sub_cancel]; exact b.2.2
    · apply Subtype.ext
      show (a : A) + (b - a) = b
      rw [add_sub_cancel]

theorem eff_zero_val : ((0 : Theses.effects A) : A) = 0 := rfl

theorem eff_one_val : ((1 : Theses.effects A) : A) = 1 := rfl

/-- Finite sums in `[0,1]_𝒜` are the sums in `𝒜`. -/
theorem isSumOf_eff_iff (l : List (Theses.effects A)) (t : Theses.effects A) :
    PCM.IsSumOf l t ↔ (t : A) = (l.map Subtype.val).sum := by
  induction l generalizing t with
  | nil =>
    rw [PCM.isSumOf_nil_iff]
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext h
  | cons a l ih =>
    rw [PCM.isSumOf_cons_iff]
    constructor
    · rintro ⟨s, hs, hp, rfl⟩
      rw [List.map_cons, List.sum_cons, ← (ih s).1 hs]
      rfl
    · intro h
      rw [List.map_cons, List.sum_cons] at h
      have hl0 : 0 ≤ (l.map Subtype.val).sum :=
        List.sum_nonneg (by
          intro x hx
          obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
          exact y.2.1)
      have hl1 : (l.map Subtype.val).sum ≤ 1 := by
        refine le_trans ?_ t.2.2
        rw [h]; exact le_add_of_nonneg_left a.2.1
      refine ⟨⟨_, hl0, hl1⟩, (ih _).2 rfl, ?_, ?_⟩
      · show (a : A) + (l.map Subtype.val).sum ≤ 1
        rw [← h]; exact t.2.2
      · exact Subtype.ext h.symm

theorem finSum_eff_iff {J : Type} (x : J → Theses.effects A) (F : Finset J)
    (t : Theses.effects A) : FinSum x F t ↔ (t : A) = ∑ j ∈ F, (x j : A) := by
  unfold FinSum
  rw [isSumOf_eff_iff, List.map_map]
  exact iff_of_eq (congrArg _ (Finset.sum_map_toList F _))

/-- The finite partial sum `∑_{j∈F} x_j` as an effect. -/
def effPS {J : Type} (x : J → Theses.effects A) (F : Finset J)
    (h : ∑ j ∈ F, (x j : A) ≤ 1) : Theses.effects A :=
  ⟨∑ j ∈ F, (x j : A), Finset.sum_nonneg fun j _ => (x j).2.1, h⟩

theorem finSum_eff_exists {J : Type} (x : J → Theses.effects A) (F : Finset J)
    (h : ∑ j ∈ F, (x j : A) ≤ 1) : FinSum x F (effPS x F h) :=
  (finSum_eff_iff x F _).2 rfl

theorem csummable_eff_iff {J : Type} (x : J → Theses.effects A) :
    CSummable x ↔ ∀ F : Finset J, ∑ j ∈ F, (x j : A) ≤ 1 := by
  constructor
  · intro h F
    obtain ⟨t, ht⟩ := h F
    rw [← (finSum_eff_iff x F t).1 ht]; exact t.2.2
  · intro h F
    exact ⟨_, finSum_eff_exists x F (h F)⟩

/-- A monotone net of effects has a supremum in `𝒜` (an effect), to which it
converges ultraweakly. -/
theorem eff_exists_lub {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → A) (hmono : Monotone f) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    ∃ s : A, IsLUB (Set.range f) s ∧ Theses.A.VN.UWTendsto f Filter.atTop s ∧ 0 ≤ s ∧ s ≤ 1 := by
  obtain ⟨s, hs, hlim⟩ := Theses.B.Dils.wit_uwTendsto_of_monotone f hmono
    (fun i => IsSelfAdjoint.of_nonneg (h0 i)) h1
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact ⟨s, hs, hlim, (h0 i₀).trans (hs.1 ⟨i₀, rfl⟩), hs.2 (by rintro _ ⟨i, rfl⟩; exact h1 i)⟩

/-- **SIG 15** (`ex:wstar`, main.tex:566), predicates; **SIG 46**
(main.tex:1260): `[0,1]_𝒜` is a σ-effect algebra
(the supremum of an increasing sequence of effects is its supremum in `𝒜`). -/
theorem effects_omegaComplete (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] : OmegaComplete (Theses.effects A) := by
  intro a ha
  have hmono : Monotone fun n => (a n : A) :=
    monotone_nat_of_le_succ fun n => (eff_le_iff _ _).1 (ha n)
  obtain ⟨s, hs, -, h0, h1⟩ := eff_exists_lub (fun n => (a n : A)) hmono
    (fun n => (a n).2.1) (fun n => (a n).2.2)
  refine ⟨⟨s, h0, h1⟩, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (eff_le_iff _ _).2 (hs.1 ⟨n, rfl⟩)
  · intro c hc
    refine (eff_le_iff _ _).2 (hs.2 ?_)
    rintro _ ⟨n, rfl⟩
    exact (eff_le_iff _ _).1 (hc _ ⟨n, rfl⟩)

/-- The canonical countable sums of `[0,1]_𝒜`: `x` sums to `s` iff all
finite partial sums stay below `1` and `s` is their supremum in `𝒜`. -/
theorem isCSum_eff_iff {J : Type} (x : J → Theses.effects A) (s : Theses.effects A) :
    IsCSum x s ↔ (∀ F : Finset J, ∑ j ∈ F, (x j : A) ≤ 1) ∧
      IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (x j : A)) (s : A) := by
  have hmono : Monotone fun F : Finset J => ∑ j ∈ F, (x j : A) := fun F G hFG =>
    Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ => (x j).2.1
  constructor
  · rintro ⟨hc, hsup⟩
    have hb := (csummable_eff_iff x).1 hc
    refine ⟨hb, ?_, fun u hu => ?_⟩
    · rintro _ ⟨F, rfl⟩
      exact (eff_le_iff (effPS x F (hb F)) s).1 (hsup.1 _ ⟨F, finSum_eff_exists x F (hb F)⟩)
    · obtain ⟨w, hw, -, h0, h1⟩ := eff_exists_lub _ hmono
        (fun F => Finset.sum_nonneg fun j _ => (x j).2.1) hb
      refine le_trans ?_ (hw.2 hu)
      refine (eff_le_iff s ⟨w, h0, h1⟩).1 (hsup.2 _ ?_)
      rintro t ⟨F, hF⟩
      rw [eff_le_iff, (finSum_eff_iff x F t).1 hF]
      exact hw.1 ⟨F, rfl⟩
  · rintro ⟨hb, hlub⟩
    refine ⟨(csummable_eff_iff x).2 hb, ?_, fun c hc => ?_⟩
    · rintro t ⟨F, hF⟩
      rw [eff_le_iff, (finSum_eff_iff x F t).1 hF]
      exact hlub.1 ⟨F, rfl⟩
    · rw [eff_le_iff]
      refine hlub.2 ?_
      rintro _ ⟨F, rfl⟩
      exact (eff_le_iff (effPS x F (hb F)) c).1 (hc _ ⟨F, finSum_eff_exists x F (hb F)⟩)

/-- The canonical σ-PAM on `[0,1]_𝒜`. -/
noncomputable instance effSigmaPAM (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] : SigmaPAM (Theses.effects A) :=
  canonicalSigmaPAM (effects_omegaComplete A)

theorem eff_sumsTo_iff {J : Type} [Countable J] (x : J → Theses.effects A)
    (s : Theses.effects A) : SumsTo x s ↔ (∀ F : Finset J, ∑ j ∈ F, (x j : A) ≤ 1) ∧
      IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (x j : A)) (s : A) :=
  (canonical_sumsTo_iff _ x s).trans (isCSum_eff_iff x s)

end Effects

/-! ## SIG 15: the hom-sets of `W*_cpsuᵒᵖ` as σ-PAMs -/

section WHoms

open Theses.A.VN (UWTendsto)

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem ncpsu_mono (f : Theses.NCPSUMap A B) {a b : A} (h : a ≤ b) :
    f.toNCPMap a ≤ f.toNCPMap b :=
  OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap h

theorem ncpsu_nonneg (f : Theses.NCPSUMap A B) {a : A} (h : 0 ≤ a) : 0 ≤ f.toNCPMap a := by
  have := ncpsu_mono f h
  rwa [ncp_zero_apply] at this

/-- ncpsu-maps send effects to effects. -/
theorem ncpsu_mem_effects (f : Theses.NCPSUMap A B) {b : A} (hb : b ∈ Theses.effects A) :
    f.toNCPMap b ∈ Theses.effects B :=
  ⟨ncpsu_nonneg f hb.1, (ncpsu_mono f hb.2).trans f.subunital'⟩

/-- A positive element is a positive multiple of an effect. -/
theorem exists_effect_smul {a : A} (ha : 0 ≤ a) :
    ∃ (n : ℝ) (e : A), e ∈ Theses.effects A ∧ a = (n : ℂ) • e := by
  set n : ℝ := ‖a‖ + 1 with hn
  have hn0 : 0 < n := by positivity
  refine ⟨n, ((n⁻¹ : ℝ) : ℂ) • a, ⟨?_, ?_⟩, ?_⟩
  · exact Theses.A.CStar.cstar_positive_1 a ha _ (inv_nonneg.mpr hn0.le)
  · have h1 : a ≤ ((‖a‖ : ℝ) : ℂ) • (1 : A) := by
      rw [Complex.coe_smul]; exact Theses.A.VN.le_norm_smul_one ha
    refine (smul_le_smul_cstar (inv_nonneg.mpr hn0.le) h1).trans ?_
    rw [smul_smul, ← Complex.ofReal_mul]
    refine smul_one_le_one (mul_nonneg (inv_nonneg.mpr hn0.le) (norm_nonneg a)) ?_
    rw [inv_mul_le_iff₀ hn0]; linarith
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn0.ne', Complex.ofReal_one, one_smul]

/-- ncpsu-maps agreeing on effects are equal. -/
theorem ncpsu_ext_effects {f g : Theses.NCPSUMap A B}
    (h : ∀ b ∈ Theses.effects A, f.toNCPMap b = g.toNCPMap b) : f = g := by
  refine ncpsu_ext fun a => ?_
  have := linear_eq_zero_of_nonneg (f := ncpLin f.toNCPMap - ncpLin g.toNCPMap) (fun c hc => by
    obtain ⟨n, e, he, rfl⟩ := exists_effect_smul hc
    simp only [LinearMap.sub_apply, ncpLin_apply, ncp_smul_apply, h e he, sub_self]) a
  simpa [sub_eq_zero] using this

variable {X Y : WStarCPSU.{u}ᵒᵖ}

/-- Evaluation of a map `f : X ⟶ Y` of `W*_cpsuᵒᵖ` (an ncpsu-map
`Y → X`) at the effects of `Y`. -/
noncomputable def vnEv (f : X ⟶ Y) (b : Theses.effects Y.unop.base) : Theses.effects X.unop.base :=
  ⟨f.unop.toNCPMap b, ncpsu_mem_effects f.unop b.2⟩

theorem vnEv_val (f : X ⟶ Y) (b : Theses.effects Y.unop.base) :
    (vnEv f b : X.unop.base) = f.unop.toNCPMap b := rfl

/-- The key existence statement: a family of ncpsu-maps whose finite partial
sums at `1` stay below `1` has an ultraweak sum, which is again ncpsu, and
whose value at an effect is the supremum of the partial sums. -/
theorem vn_exists_sum {J : Type} (f : J → (X ⟶ Y))
    (hb : ∀ F : Finset J, ∑ j ∈ F, (f j).unop.toNCPMap 1 ≤ 1) :
    ∃ g : X ⟶ Y, (∀ b, UWTendsto (fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b)
        Filter.atTop (g.unop.toNCPMap b)) ∧
      ∀ b ∈ Theses.effects Y.unop.base,
        IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b) (g.unop.toNCPMap b) := by
  classical
  obtain ⟨L, hL⟩ := Theses.B.Dils.exists_ncp_uwsum (fun j => (f j).unop.toNCPMap) 1 hb
  have hlub : ∀ b ∈ Theses.effects Y.unop.base,
      IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b) (L b) := by
    intro b hbe
    have hmono : Monotone fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b := fun F G hFG =>
      Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ => ncpsu_nonneg _ hbe.1
    obtain ⟨s, hs, hlim, -, -⟩ := eff_exists_lub _ hmono
      (fun F => Finset.sum_nonneg fun j _ => ncpsu_nonneg _ hbe.1)
      (fun F => (Finset.sum_le_sum fun j _ => ncpsu_mono _ hbe.2).trans (hb F))
    rwa [Theses.A.VN.uwTendsto_unique (hL b) hlim]
  have hsu : L 1 ≤ 1 :=
    (hlub 1 ⟨zero_le_one, le_rfl⟩).2 (by rintro _ ⟨F, rfl⟩; exact hb F)
  exact ⟨Quiver.Hom.op (show Y.unop ⟶ X.unop from ⟨L, hsu⟩), hL, hlub⟩

theorem vn_pSumsTo_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) (g : X ⟶ Y) :
    PSumsTo vnEv f g ↔ (∀ F : Finset J, ∑ j ∈ F, (f j).unop.toNCPMap 1 ≤ 1) ∧
      ∀ b ∈ Theses.effects Y.unop.base,
        IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b) (g.unop.toNCPMap b) := by
  constructor
  · intro h
    refine ⟨((eff_sumsTo_iff _ _).1 (h 1)).1, fun b hb => ((eff_sumsTo_iff _ _).1 (h ⟨b, hb⟩)).2⟩
  · rintro ⟨hb, hlub⟩ b
    refine (eff_sumsTo_iff _ _).2 ⟨fun F => ?_, hlub b b.2⟩
    exact (Finset.sum_le_sum fun j _ => ncpsu_mono _ b.2.2).trans (hb F)

/-- The data of the σ-PAM of ultraweak sums on `W*_cpsuᵒᵖ(X, Y)`. -/
theorem vnHomData (X Y : WStarCPSU.{u}ᵒᵖ) : PointwiseData (vnEv (X := X) (Y := Y)) where
  inj f g h := Quiver.Hom.unop_inj (ncpsu_ext_effects fun b hb =>
    congrArg Subtype.val (congrFun h ⟨b, hb⟩))
  nonempty := ⟨Quiver.Hom.op (show Y.unop ⟶ X.unop from wZeroSU _ _)⟩
  sub f P := by
    rintro ⟨g, hg⟩
    have hb := ((vn_pSumsTo_iff f g).1 hg).1
    obtain ⟨g', hg', hlub⟩ := vn_exists_sum (fun j : {j // P j} => f j.1) fun F => by
      have := hb (F.map (Function.Embedding.subtype P))
      rwa [Finset.sum_map] at this
    exact ⟨g', (vn_pSumsTo_iff _ _).2 ⟨fun F => by
      have := hb (F.map (Function.Embedding.subtype P))
      rwa [Finset.sum_map] at this, hlub⟩⟩
  lim f h := by
    have hb : ∀ F : Finset _, ∑ j ∈ F, (f j).unop.toNCPMap 1 ≤ 1 := by
      intro F
      obtain ⟨g, hg⟩ := h F
      have := ((vn_pSumsTo_iff _ g).1 hg).1 Finset.univ
      rwa [Finset.sum_coe_sort F (fun j => (f j).unop.toNCPMap 1)] at this
    obtain ⟨g, -, hlub⟩ := vn_exists_sum f hb
    exact ⟨g, (vn_pSumsTo_iff f g).2 ⟨hb, hlub⟩⟩

/-- **SIG 15** (`ex:wstar`, main.tex:554): the σ-PAM on the hom-sets of
`W*_cpsuᵒᵖ`: ultraweak sums of ncpsu-maps. -/
noncomputable instance vnHomSigmaPAM (X Y : WStarCPSU.{u}ᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  pointwiseSigmaPAM (vnHomData X Y)

/-- **SIG 15** (`ex:wstar`, main.tex:554, Example), the sums as printed: a
countable family `f_j : 𝔄 → 𝔅` in `W*ᵒᵖ` (ncpsu-maps `𝔅 → 𝔄`) sums to `g`
iff `∑_{j∈F} f_j(1) ≤ 1` for every finite `F` and `g(b) = ∑_j f_j(b)` for all
`b`, the sum converging ultraweakly (as the net of finite partial sums). -/
theorem vn_sumsTo_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) (g : X ⟶ Y) :
    SumsTo f g ↔ (∀ F : Finset J, ∑ j ∈ F, (f j).unop.toNCPMap 1 ≤ 1) ∧
      ∀ b, UWTendsto (fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b) Filter.atTop
        (g.unop.toNCPMap b) := by
  rw [pointwise_sumsTo_iff, vn_pSumsTo_iff]
  constructor
  · rintro ⟨hb, hlub⟩
    obtain ⟨g', hg', hlub'⟩ := vn_exists_sum f hb
    have : g = g' := Quiver.Hom.unop_inj (ncpsu_ext_effects fun b hb' =>
      (hlub b hb').unique (hlub' b hb'))
    subst this
    exact ⟨hb, hg'⟩
  · rintro ⟨hb, hlim⟩
    obtain ⟨g', hg', hlub'⟩ := vn_exists_sum f hb
    have : g = g' := Quiver.Hom.unop_inj (ncpsu_ext fun b =>
      Theses.A.VN.uwTendsto_unique (hlim b) (hg' b))
    subst this
    exact ⟨hb, hlub'⟩

/-- **SIG 15** (`ex:wstar`, main.tex:554, Example): a countable family is
summable iff `∑_{j∈F} f_j(1) ≤ 1` for every finite `F ⊆ J`. -/
theorem vn_summable_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) :
    Summable f ↔ ∀ F : Finset J, ∑ j ∈ F, (f j).unop.toNCPMap 1 ≤ 1 := by
  constructor
  · intro h; exact ((vn_sumsTo_iff f _).1 (sumsTo_sum h)).1
  · intro hb
    obtain ⟨g, hg, -⟩ := vn_exists_sum f hb
    exact ((vn_sumsTo_iff f g).2 ⟨hb, hg⟩).summable

theorem vn_sumsTo_apply {J : Type} [Countable J] {f : J → (X ⟶ Y)} {g : X ⟶ Y}
    (h : SumsTo f g) {b : Y.unop.base} (hb : b ∈ Theses.effects Y.unop.base) :
    IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (f j).unop.toNCPMap b) (g.unop.toNCPMap b) :=
  ((vn_pSumsTo_iff f g).1 ((pointwise_sumsTo_iff _ f g).1 h)).2 b hb

end WHoms

/-! ## SIG 15: countable coproducts of `W*_cpsuᵒᵖ`

The coproduct of `(𝒜_j)_j` in `W*_cpsuᵒᵖ` is the ℓ^∞-direct sum `⊕_j 𝒜_j`
(the product in `W*_cpsu`, tree **47IV**).  Mathlib's unital C*-structure on
`lp` needs non-zero summands, so the sum is taken over the `j` with `𝒜_j`
non-trivial; the zero summands contribute nothing (every map into the zero
algebra is `0`). -/

section Coproducts

open Theses.A.VN (UWTendsto)

variable {J : Type} (X : J → WStarCPSU.{u}ᵒᵖ)

/-- The summands. -/
abbrev vnFam (j : J) : Type u := (X j).unop.base.carrier

/-- The index set of the non-trivial summands. -/
abbrev vnIdx : Type := {j : J // Nontrivial (vnFam X j)}

instance vnFam_nontrivial (k : vnIdx X) : Nontrivial (vnFam X k.1) := k.2

/-- The direct sum `⊕_j 𝒜_j` (over the non-trivial summands). -/
abbrev vnSumAlg : Type u := ↥(lp (fun k : vnIdx X => vnFam X k.1) ∞)

/-- The coproduct object `∐_j 𝒜_j` of `W*_cpsuᵒᵖ`. -/
noncomputable abbrev vnSum : WStarCPSU.{u}ᵒᵖ := op (WStarCPSU.of (WStar.of (vnSumAlg X)))

open Classical in
/-- The projection `π_j : ⊕_k 𝒜_k → 𝒜_j` (zero on a zero summand). -/
noncomputable def vnProj (j : J) : Theses.NCPSUMap (vnSumAlg X) (vnFam X j) :=
  if h : Nontrivial (vnFam X j) then
    ⟨Theses.A.Proc.nmiuNCP (Theses.B.Dils.lpProjNMIU (𝒜 := fun k : vnIdx X => vnFam X k.1) ⟨j, h⟩),
      le_of_eq (map_one (Theses.B.Dils.lpProjNMIU (𝒜 := fun k : vnIdx X => vnFam X k.1)
        ⟨j, h⟩).toStarAlgHom)⟩
  else wZeroSU _ _

/-- The `k`-th coordinate of an element of `⊕_j 𝒜_j`. -/
def vnCoord (a : vnSumAlg X) (k : vnIdx X) : vnFam X k.1 := (a : ∀ k : vnIdx X, vnFam X k.1) k

theorem vnProj_apply (j : J) (h : Nontrivial (vnFam X j)) (a : vnSumAlg X) :
    (vnProj X j).toNCPMap a = vnCoord X a ⟨j, h⟩ := by
  unfold vnProj
  rw [dite_eq_left h]
  rfl

/-- The coprojection `𝒜_j ⟶ ∐_k 𝒜_k` of `W*_cpsuᵒᵖ`. -/
noncomputable def vnProjOp (j : J) : X j ⟶ vnSum X :=
  Quiver.Hom.op (show (vnSum X).unop ⟶ (X j).unop from vnProj X j)

/-- The coproduct cofan. -/
noncomputable def vnCofan : Cofan X := Cofan.mk (vnSum X) (vnProjOp X)

theorem vnCofan_inj (j : J) : (vnCofan X).inj j = vnProjOp X j := rfl

theorem subsingleton_of_not_nontrivial {j : J} (h : ¬ Nontrivial (vnFam X j)) :
    Subsingleton (vnFam X j) := not_nontrivial_iff_subsingleton.mp h

/-- The cotupling: the tupling of ncpsu-maps into `⊕_j 𝒜_j` (tree **47IV**). -/
noncomputable def vnDesc (t : Cofan X) : (vnCofan X).pt ⟶ t.pt :=
  Quiver.Hom.op (show t.pt.unop ⟶ (vnSum X).unop from
    (Theses.A.VN.vn_products_ncpsu' (𝒜 := vnFam X) (B := t.pt.unop.base.carrier)
      (fun k => (t.inj k.1).unop)).exists.choose)

theorem vnDesc_apply (t : Cofan X) (k : vnIdx X) (b : t.pt.unop.base) :
    vnCoord X ((vnDesc X t).unop.toNCPMap b) k =
      (t.inj k.1).unop.toNCPMap b :=
  (Theses.A.VN.vn_products_ncpsu' (𝒜 := vnFam X) (B := t.pt.unop.base.carrier)
      (fun k => (t.inj k.1).unop)).exists.choose_spec k b

/-- **SIG 15** (`ex:wstar`, main.tex:548): `⊕_j 𝒜_j` is the coproduct of
the `𝒜_j` in `W*_cpsuᵒᵖ`. -/
noncomputable def vnCofanIsColimit : IsColimit (vnCofan X) :=
  Cofan.IsColimit.mk _ (vnDesc X)
    (fun t j => by
      apply suop_hom_ext
      intro b
      erw [suop_comp_apply]
      by_cases h : Nontrivial (vnFam X j)
      · rw [vnCofan_inj]
        exact (vnProj_apply X j h _).trans (vnDesc_apply X t ⟨j, h⟩ b)
      · have := subsingleton_of_not_nontrivial X h
        exact Subsingleton.elim (α := vnFam X j) _ _)
    (fun t m hm => by
      apply Quiver.Hom.unop_inj
      refine (Theses.A.VN.vn_products_ncpsu' (𝒜 := vnFam X) (B := t.pt.unop.base.carrier)
        (fun k => (t.inj k.1).unop)).unique (y₁ := m.unop) ?_ ?_
      · intro k b
        have := suop_congr (hm k.1) b
        erw [suop_comp_apply] at this
        exact (vnProj_apply X k.1 k.2 _).symm.trans this
      · exact (Theses.A.VN.vn_products_ncpsu' (𝒜 := vnFam X) (B := t.pt.unop.base.carrier)
          (fun k => (t.inj k.1).unop)).exists.choose_spec)

end Coproducts

/-- **SIG 15** (`ex:wstar`, main.tex:548): `W*_cpsuᵒᵖ` has countable
coproducts (indeed all small ones), the ℓ^∞-direct sums. -/
instance vnHasCountableCoproducts : HasCountableCoproducts WStarCPSU.{u}ᵒᵖ :=
  ⟨fun J _ => ⟨fun F => by
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      HasColimit.mk ⟨_, vnCofanIsColimit (F.obj ∘ Discrete.mk)⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor⟩⟩

/-! ## SIG 15: `W*_cpsuᵒᵖ` is a σ-effectus -/

section WEffectus

open Theses.A.VN (UWTendsto)

variable {X Y : WStarCPSU.{u}ᵒᵖ}

theorem uwTendsto_of_eventually_eq {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {ι : Type*} {l : Filter ι} {x : ι → A} {a : A}
    (h : ∀ᶠ i in l, x i = a) : UWTendsto x l a := by
  let _ : TopologicalSpace A := Theses.A.VN.ultraweak A
  exact tendsto_nhds_of_eventually_eq h

/-- The zero map of the σ-PAM (the empty sum) is the zero ncpsu-map. -/
theorem vn_zero_eq (X Y : WStarCPSU.{u}ᵒᵖ) :
    (0 : X ⟶ Y) = Quiver.Hom.op (show Y.unop ⟶ X.unop from wZeroSU _ _) := by
  have h := (vn_sumsTo_iff (Empty.elim : Empty → (X ⟶ Y)) _).1 (sumsTo_of_isEmpty _)
  apply suop_hom_ext
  intro b
  refine (Theses.A.VN.uwTendsto_unique (h.2 b) (uwTendsto_of_eventually_eq ?_)).trans
    (wZeroSU_apply (A := Y.unop.base.carrier) (B := X.unop.base.carrier) b).symm
  exact Filter.Eventually.of_forall fun F => by
    rw [Finset.eq_empty_of_isEmpty F, Finset.sum_empty]

theorem vn_zero_apply (b : Y.unop.base) : (0 : X ⟶ Y).unop.toNCPMap b = 0 := by
  rw [vn_zero_eq]; rfl

/-- Binary sums: `f ⊥ g` iff `f(1) + g(1) ≤ 1` (the tree's `suPCM`). -/
theorem vn_perp_iff (f g : X ⟶ Y) :
    Perp f g ↔ f.unop.toNCPMap 1 + g.unop.toNCPMap 1 ≤ 1 := by
  show SigmaPAM.Summable ![f, g] ↔ _
  rw [vn_summable_iff]
  constructor
  · intro h
    have := h Finset.univ
    rwa [Fin.sum_univ_two] at this
  · intro h F
    refine le_trans ?_ h
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (f := fun j => (![f, g] j).unop.toNCPMap 1) fun j _ _ => ncpsu_one_nonneg _
    simpa [Fin.sum_univ_two] using this

/-- Binary sums are pointwise sums (the tree's `suPCM`). -/
theorem vn_ovee_apply {f g : X ⟶ Y} (h : Perp f g) (b : Y.unop.base) :
    (ovee f g h).unop.toNCPMap b = f.unop.toNCPMap b + g.unop.toNCPMap b := by
  have hs := (vn_sumsTo_iff ![f, g] _).1 (sumsTo_sum (show SigmaPAM.Summable ![f, g] from h))
  refine Theses.A.VN.uwTendsto_unique (hs.2 b) (uwTendsto_of_eventually_eq ?_)
  refine Filter.eventually_atTop.2 ⟨Finset.univ, fun F hF => ?_⟩
  rw [Finset.eq_univ_of_forall fun j => hF (Finset.mem_univ j), Fin.sum_univ_two]
  rfl

/-- A split mono `i` of `W*_cpsuᵒᵖ` (an ncpsu-map with a right inverse) is
unital. -/
theorem vn_one_of_retraction {X Y : WStarCPSU.{u}ᵒᵖ} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) :
    i.unop.toNCPMap 1 = 1 := by
  have h1 : i.unop.toNCPMap (r.unop.toNCPMap 1) = 1 := by
    rw [← suop_comp_apply, h]; exact su_id_apply _
  refine le_antisymm i.unop.subunital' ?_
  calc (1 : X.unop.base) = i.unop.toNCPMap (r.unop.toNCPMap 1) := h1.symm
    _ ≤ i.unop.toNCPMap 1 := ncpsu_mono _ r.unop.subunital'

theorem vn_inl_one (B : WStarCPSU.{u}ᵒᵖ) : (coprod.inl : B ⟶ B ⨿ B).unop.toNCPMap 1 = 1 :=
  vn_one_of_retraction _ (coprod.desc (𝟙 B) (𝟙 B)) (coprod.inl_desc _ _)

theorem vn_inr_one (B : WStarCPSU.{u}ᵒᵖ) : (coprod.inr : B ⟶ B ⨿ B).unop.toNCPMap 1 = 1 :=
  vn_one_of_retraction _ (coprod.desc (𝟙 B) (𝟙 B)) (coprod.inr_desc _ _)

section PProj

variable {J : Type} [Countable J] (X : J → WStarCPSU.{u}ᵒᵖ)

/-- The chosen coproduct is `⊕_j 𝒜_j`. -/
noncomputable def vnCoprodIso : ∐ X ≅ vnSum X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (vnCofanIsColimit X)

theorem ι_vnCoprodIso (k : J) :
    Sigma.ι X k ≫ (vnCoprodIso X).hom = (vnCofan X).inj k :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk k)

theorem vnKappa_le_one (j : J) (h : Nontrivial (vnFam X j)) :
    Theses.A.Proc.lpKappa (𝒜 := fun k : vnIdx X => vnFam X k.1) ⟨j, h⟩ 1 ≤ 1 := by
  classical
  rw [Theses.A.VN.lp_infty_le_iff]
  intro k
  by_cases hk : k = ⟨j, h⟩
  · subst hk
    rw [Theses.A.Proc.lpKappa_apply_self, lp.infty_coeFn_one]; rfl
  · rw [Theses.A.Proc.lpKappa_apply_ne _ _ hk, lp.infty_coeFn_one]; exact zero_le_one

/-- The coprojection `κ_j : 𝒜_j → ⊕_k 𝒜_k` (for a non-zero summand). -/
noncomputable def vnKappa (j : J) (h : Nontrivial (vnFam X j)) :
    Theses.NCPSUMap (vnFam X j) (vnSumAlg X) :=
  ⟨Theses.B.Dils.lpKappaNCP (𝒜 := fun k : vnIdx X => vnFam X k.1) ⟨j, h⟩, vnKappa_le_one X j h⟩

theorem vnKappa_apply (j : J) (h : Nontrivial (vnFam X j)) (a : vnFam X j) :
    (vnKappa X j h).toNCPMap a = Theses.A.Proc.lpKappa (𝒜 := fun k : vnIdx X => vnFam X k.1) ⟨j, h⟩ a :=
  rfl

/-- `κ_j` as a map `∐_k 𝒜_k ⟶ 𝒜_j` of `W*_cpsuᵒᵖ`. -/
noncomputable def vnKappaOp (j : J) (h : Nontrivial (vnFam X j)) : vnSum X ⟶ X j :=
  Quiver.Hom.op (show (X j).unop ⟶ (vnSum X).unop from vnKappa X j h)

/-- The partial projections of `∐_j 𝒜_j` are the coprojections `κ_j` of
`⊕_j 𝒜_j`. -/
theorem vn_pproj_eq (j : J) (h : Nontrivial (vnFam X j)) :
    pproj X j = (vnCoprodIso X).hom ≫ vnKappaOp X j h := by
  classical
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_vnCoprodIso]
  by_cases hk : k = j
  · subst hk
    rw [ι_pproj_self]
    apply suop_hom_ext
    intro a
    erw [suop_comp_apply, unop_id, su_id_apply]
    show a = (vnProj X k).toNCPMap ((vnKappa X k h).toNCPMap a)
    symm
    rw [vnProj_apply X k h, vnKappa_apply]
    exact Theses.A.Proc.lpKappa_apply_self _ _
  · rw [ι_pproj_ne _ hk]
    apply suop_hom_ext
    intro a
    erw [suop_comp_apply]
    rw [vn_zero_apply]
    show 0 = (vnProj X k).toNCPMap ((vnKappa X j h).toNCPMap a)
    symm
    by_cases hk' : Nontrivial (vnFam X k)
    · rw [vnProj_apply X k hk', vnKappa_apply]
      exact Theses.A.Proc.lpKappa_apply_ne _ _ (fun e => hk (congrArg Subtype.val e))
    · have := subsingleton_of_not_nontrivial X hk'
      exact Subsingleton.elim (α := vnFam X k) _ _

end PProj

/-- **SIG 15** (`ex:wstar`, main.tex:548): `W*_cpsuᵒᵖ` is a σ-PAC: the
countable coproducts are the direct sums, composition is σ-biadditive for
the ultraweak sums (normal maps are ultraweakly continuous), compatible
families are summable, and untying holds. -/
instance vnSigmaPAC : SigmaPAC WStarCPSU.{u}ᵒᵖ where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · rw [vn_sumsTo_iff] at hs ⊢
      refine ⟨fun F => ?_, fun b => ?_⟩
      · simp only [suop_comp_apply]
        exact (Finset.sum_le_sum fun j _ => ncpsu_mono _ g.unop.subunital').trans (hs.1 F)
      · simp only [suop_comp_apply]
        exact hs.2 _
    · rw [vn_sumsTo_iff] at hs ⊢
      have hsum : ∀ (F : Finset _) (b : Z.unop.base), ∑ j ∈ F, (f ≫ x j).unop.toNCPMap b =
          f.unop.toNCPMap (∑ j ∈ F, (x j).unop.toNCPMap b) := fun F b => by
        simp only [suop_comp_apply]
        exact (map_sum (ncpLin f.unop.toNCPMap) _ F).symm
      refine ⟨fun F => ?_, fun b => ?_⟩
      · rw [hsum]
        exact (ncpsu_mono _ (hs.1 F)).trans f.unop.subunital'
      · have := (@Continuous.tendsto _ _ (Theses.A.VN.ultraweak _) (Theses.A.VN.ultraweak _) _
          (Theses.B.Dils.wit_ncp_continuous f.unop.toNCPMap) _).comp (hs.2 b)
        rw [suop_comp_apply]
        exact this.congr fun F => (hsum F b).symm
  compatible_sum {J} _ {A B} f := by
    rintro ⟨g, hg⟩
    rw [vn_summable_iff]
    intro F
    by_cases hB : Nontrivial B.unop.base.carrier
    · let X : J → WStarCPSU.{u}ᵒᵖ := fun _ => B
      let H : Theses.NCPSUMap (vnSumAlg X) A.unop.base.carrier := (g ≫ (vnCoprodIso X).hom).unop
      have hval : ∀ j, (f j).unop.toNCPMap 1 = H.toNCPMap ((vnKappa X j hB).toNCPMap 1) := by
        intro j
        rw [← hg j, vn_pproj_eq X j hB, ← Category.assoc]
        erw [suop_comp_apply]
        rfl
      have hsum : ∑ j ∈ F, (f j).unop.toNCPMap 1 =
          H.toNCPMap (∑ j ∈ F, (vnKappa X j hB).toNCPMap 1) := by
        rw [Finset.sum_congr rfl fun j _ => hval j]
        exact (map_sum (ncpLin H.toNCPMap) _ F).symm
      rw [hsum]
      refine (ncpsu_mono H ?_).trans H.subunital'
      classical
      rw [Theses.A.VN.lp_infty_le_iff]
      rintro ⟨k, hk⟩
      rw [lp.infty_coeFn_one, Pi.one_apply, lp.coeFn_sum, Finset.sum_apply]
      simp only [vnKappa_apply]
      by_cases hkF : k ∈ F
      · rw [Finset.sum_eq_single_of_mem k hkF fun j _ hjk =>
          Theses.A.Proc.lpKappa_apply_ne _ _ fun e => hjk (congrArg Subtype.val e).symm]
        rw [Theses.A.Proc.lpKappa_apply_self]
      · rw [Finset.sum_eq_zero fun j hj =>
          Theses.A.Proc.lpKappa_apply_ne _ _ fun e => hkF (by
            rw [show k = j from congrArg Subtype.val e]; exact hj)]
        exact zero_le_one
    · have := not_nontrivial_iff_subsingleton.mp hB
      have h0 : ∀ j, (f j).unop.toNCPMap 1 = 0 := fun j => by
        rw [show (1 : B.unop.base.carrier) = 0 from Subsingleton.elim _ _]
        exact ncp_zero_apply _
      simp only [h0, Finset.sum_const_zero]
      exact zero_le_one
  untying {A B f g} h := by
    rw [vn_summable_iff] at h ⊢
    have e : (fun j => (![f ≫ coprod.inl, g ≫ coprod.inr] j).unop.toNCPMap 1) =
        fun j => (![f, g] j).unop.toNCPMap 1 := by
      funext j
      fin_cases j
      · show (f ≫ coprod.inl).unop.toNCPMap 1 = f.unop.toNCPMap 1
        rw [suop_comp_apply, vn_inl_one]
      · show (g ≫ coprod.inr).unop.toNCPMap 1 = g.unop.toNCPMap 1
        rw [suop_comp_apply, vn_inr_one]
    intro F
    have := h F
    simp only [← e] at this ⊢
    exact this

end WEffectus

section WEffectus2

variable {X Y : WStarCPSU.{u}ᵒᵖ}

theorem vn_comp_one_apply (f : X ⟶ Y) : (f ≫ suOne Y).unop.toNCPMap 1 = f.unop.toNCPMap 1 := by
  rw [suop_comp_apply]
  exact congrArg f.unop.toNCPMap (suOne_unop_one Y)

/-- The orthocomplement `p^⊥ = 1 - p` of a predicate `p : 𝒜 ⟶ ℂ`. -/
noncomputable def vnOrth (p : X ⟶ suI) : X ⟶ suI :=
  Quiver.Hom.op (wEffect (sub_nonneg.mpr p.unop.subunital') (sub_le_self 1 (ncpsu_one_nonneg p.unop)))

theorem vnOrth_one (p : X ⟶ suI) :
    (vnOrth p).unop.toNCPMap 1 = 1 - p.unop.toNCPMap 1 := by
  show (1 : ULift.{u} ℂ).down • ((1 : X.unop.base.carrier) - p.unop.toNCPMap 1) = _
  simp

/-- **SIG 15** (`ex:wstar`, main.tex:548, Example), for completely positive
maps: the opposite of the tree's `W*_cpsu` (von Neumann algebras, normal
completely positive subunital maps) is a σ-effectus with `ℂ` as unit: the
effect object is `ℂ` (`suI`), the truth predicate `1 : 𝒜 ⟶ ℂ` the unit map
`z ↦ z·1`, `p^⊥ = 1 - p`; summability and sums are those of
`vn_summable_iff` and `vn_sumsTo_iff` (ultraweak sums).  The print's
category, with positive maps, is `pvnSigmaEffectus`. -/
noncomputable instance vnSigmaEffectus : SigmaEffectus WStarCPSU.{u}ᵒᵖ :=
  { vnSigmaPAC with
    I := suI
    one := suOne
    orth := vnOrth
    perp_orth := fun {X} p => by
      rw [vn_perp_iff, vnOrth_one]
      exact le_of_eq (add_sub_cancel _ _)
    ovee_orth := fun {X} p => by
      refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
      have hperp : Perp p (vnOrth p) := (vn_perp_iff p (vnOrth p)).2
        (by rw [vnOrth_one]; exact le_of_eq (add_sub_cancel _ _))
      have h := vn_ovee_apply hperp 1
      rw [vnOrth_one, add_sub_cancel] at h
      exact h.trans (suOne_unop_one X).symm
    orth_unique := fun {X p q} h heq => by
      refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
      have h1 := vn_ovee_apply h 1
      rw [heq, suOne_unop_one] at h1
      show q.unop.toNCPMap 1 = (vnOrth p).unop.toNCPMap 1
      rw [vnOrth_one, h1]
      abel
    eq_zero_of_perp_one := fun {X p} h => by
      rw [vn_perp_iff, suOne_unop_one] at h
      have h4 : p.unop.toNCPMap 1 = 0 :=
        le_antisymm (by simpa using sub_le_sub_right h (1 : X.unop.base.carrier))
          (ncpsu_one_nonneg p.unop)
      refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
      exact h4.trans (vn_zero_apply (X := X) (Y := suI) 1).symm
    eq_zero_of_one_zero := fun {X Y f} h => by
      have h2 : f.unop.toNCPMap 1 = 0 := by
        rw [← vn_comp_one_apply, h, vn_zero_apply]
      refine Quiver.Hom.unop_inj (ncpsu_ext fun y => ?_)
      rw [ncp_eq_zero_of_one f.unop.toNCPMap h2 y]
      exact (vn_zero_apply y).symm
    perp_of_one_perp := fun {X Y f g} h => by
      rw [vn_perp_iff, vn_comp_one_apply, vn_comp_one_apply] at h
      exact (vn_perp_iff f g).2 h }

/-- The binary sums of the σ-effectus `W*_cpsuᵒᵖ` are those of the tree's
partial-form effectus `vnPartialStructure` (`suPCM`): same orthogonality, same
sums. -/
theorem vn_pcm_eq_suPCM (f g : X ⟶ Y) :
    (Perp f g ↔ @Perp _ (suPCM X Y) f g) ∧
      ∀ (h : Perp f g) (h' : @Perp _ (suPCM X Y) f g), ovee f g h = @ovee _ (suPCM X Y) f g h' := by
  refine ⟨vn_perp_iff f g, fun h h' => Quiver.Hom.unop_inj (ncpsu_ext fun b => ?_)⟩
  rw [vn_ovee_apply]
  rfl

/-- The effect `p(1)` of a predicate `p : 𝒜 ⟶ ℂ`. -/
noncomputable def vnPredVal (p : X ⟶ suI) : Theses.effects X.unop.base :=
  ⟨p.unop.toNCPMap 1, ncpsu_one_nonneg _, p.unop.subunital'⟩

/-- The predicate `z ↦ z·a` of an effect `a`. -/
noncomputable def vnPredOf (a : Theses.effects X.unop.base) : X ⟶ suI :=
  Quiver.Hom.op (wEffect a.2.1 a.2.2)

theorem vnPredOf_one (a : Theses.effects X.unop.base) :
    (vnPredOf a).unop.toNCPMap 1 = (a : X.unop.base) :=
  (wEffect_apply a.2.1 a.2.2 1).trans (by simp)

/-- **SIG 15** (`ex:wstar`, main.tex:566): the predicates `Pred(𝔄) = W*ᵒᵖ(𝔄, ℂ)` are the
effects `[0,1]_𝔄`: `p ↦ p(1)` is a bijection onto the effects which
preserves and reflects orthogonality and sums (`p ⊥ q ⟺ p(1) + q(1) ≤ 1`,
`(p ⊕ q)(1) = p(1) + q(1)`), and sends `1` to `1`, `p^⊥` to `1 - p(1)`. -/
theorem vn_pred_effects (X : WStarCPSU.{u}ᵒᵖ) :
    (∃ e : Pred X ≃ Theses.effects X.unop.base, ∀ p, (e p : X.unop.base) = p.unop.toNCPMap 1) ∧
      (∀ p q : Pred X, Perp p q ↔ p.unop.toNCPMap 1 + q.unop.toNCPMap 1 ≤ 1) ∧
      (∀ (p q : Pred X) (h : Perp p q),
        (ovee p q h).unop.toNCPMap 1 = p.unop.toNCPMap 1 + q.unop.toNCPMap 1) ∧
      (truth X : Pred X).unop.toNCPMap 1 = 1 ∧
      ∀ p : Pred X, (orth p : Pred X).unop.toNCPMap 1 = 1 - p.unop.toNCPMap 1 := by
  refine ⟨⟨{ toFun := vnPredVal
             invFun := vnPredOf
             left_inv := fun p => Quiver.Hom.unop_inj (ncpsu_scal_ext (vnPredOf_one _))
             right_inv := fun a => Subtype.ext (vnPredOf_one a) }, fun p => rfl⟩,
    fun p q => vn_perp_iff p q, fun p q h => vn_ovee_apply h 1, suOne_unop_one X,
    fun p => vnOrth_one p⟩

/-- **SIG 15** (`ex:wstar`, main.tex:568): the total maps of `W*ᵒᵖ` are precisely the
unital maps. -/
theorem vn_isTotal_iff (f : X ⟶ Y) : IsTotal f ↔ f.unop.toNCPMap 1 = 1 := by
  show f ≫ suOne Y = suOne X ↔ _
  constructor
  · intro h
    have := vn_comp_one_apply f
    rw [h, suOne_unop_one] at this
    exact this.symm
  · intro h
    refine Quiver.Hom.unop_inj (ncpsu_scal_ext ?_)
    exact (vn_comp_one_apply f).trans (h.trans (suOne_unop_one X).symm)

/-- **SIG 15** (`ex:wstar`, main.tex:561): the states of `𝔄` in `W*ᵒᵖ` are the unital
normal (completely) positive maps `𝔄 → ℂ`, the normal states. -/
theorem vn_stat_iff (ω : suI ⟶ X) : IsTotal ω ↔ ω.unop.toNCPMap 1 = 1 := vn_isTotal_iff ω

end WEffectus2

/-! ## Scalars along a transport of σ-effectus structure -/

section TransportScalars

universe u₂ v₂ v

variable {D : Type u} [Category.{v} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasCountableCoproducts D']
  [∀ X Y : D', SigmaPAM (X ⟶ Y)]
variable {F : D' ⥤ D} [F.Full] [F.Faithful] (hsum : SumsCompatible F)
  (I' : D') (e : F.obj I' ≅ SigmaEffectus.«I» (C := D))
  (hpres : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F)

omit [HasCountableCoproducts D] [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
  [HasCountableCoproducts D'] [∀ X Y : D', SigmaPAM (X ⟶ Y)] in
theorem transport_aux_mul (F : D' ⥤ D) {X : D'} {Y : D} (e : F.obj X ≅ Y) (m l : X ⟶ X) :
    e.inv ≫ F.map (m ≫ l) ≫ e.hom = (e.inv ≫ F.map m ≫ e.hom) ≫ (e.inv ≫ F.map l ≫ e.hom) := by
  simp

omit [HasCountableCoproducts D] [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
  [HasCountableCoproducts D'] [∀ X Y : D', SigmaPAM (X ⟶ Y)] in
theorem transport_aux_mul' (F : D' ⥤ D) [F.Full] [F.Faithful] {X : D'} {Y : D} (e : F.obj X ≅ Y)
    (m l : Y ⟶ Y) :
    F.preimage (e.hom ≫ (m ≫ l) ≫ e.inv) = F.preimage (e.hom ≫ m ≫ e.inv) ≫ F.preimage (e.hom ≫ l ≫ e.inv) := by
  apply F.map_injective
  simp

omit [HasCountableCoproducts D] [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
  [HasCountableCoproducts D'] [∀ X Y : D', SigmaPAM (X ⟶ Y)] in
theorem transport_aux_inv (F : D' ⥤ D) [F.Full] [F.Faithful] {X : D'} {Y : D} (e : F.obj X ≅ Y)
    (p : X ⟶ X) : F.preimage (e.hom ≫ (e.inv ≫ F.map p ≫ e.hom) ≫ e.inv) = p := by
  apply F.map_injective
  simp

omit [HasCountableCoproducts D] [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
  [HasCountableCoproducts D'] [∀ X Y : D', SigmaPAM (X ⟶ Y)] in
theorem transport_aux_inv' (F : D' ⥤ D) [F.Full] [F.Faithful] {X : D'} {Y : D} (e : F.obj X ≅ Y)
    (q : Y ⟶ Y) : e.inv ≫ F.map (F.preimage (e.hom ≫ q ≫ e.inv)) ≫ e.hom = q := by
  simp

include hsum in
theorem SumsCompatible.aux_perp (p q : I' ⟶ I') (h : Perp p q) :
    Perp (e.inv ≫ F.map p ≫ e.hom) (e.inv ≫ F.map q ≫ e.hom) := by
  have h1 := (hsum.perp_iff p q).1 h
  obtain ⟨h2, -⟩ := FinPAC.comp_ovee h1 e.hom
  obtain ⟨h3, -⟩ := FinPAC.ovee_comp h2 e.inv
  exact h3

include hsum in
theorem SumsCompatible.aux_ovee (p q : I' ⟶ I') (h : Perp p q)
    (h' : Perp (e.inv ≫ F.map p ≫ e.hom) (e.inv ≫ F.map q ≫ e.hom)) :
    e.inv ≫ F.map (ovee p q h) ≫ e.hom = ovee (e.inv ≫ F.map p ≫ e.hom) (e.inv ≫ F.map q ≫ e.hom) h' := by
  have h1 := (hsum.perp_iff p q).1 h
  obtain ⟨h2, e2⟩ := FinPAC.comp_ovee h1 e.hom
  obtain ⟨h3, e3⟩ := FinPAC.ovee_comp h2 e.inv
  rw [hsum.map_ovee h, e2, e3]

include hsum in
theorem SumsCompatible.aux_perp' (p q : SigmaEffectus.«I» (C := D) ⟶ SigmaEffectus.«I» (C := D))
    (h : Perp p q) : Perp (F.preimage (e.hom ≫ p ≫ e.inv)) (F.preimage (e.hom ≫ q ≫ e.inv)) := by
  rw [hsum.perp_iff, F.map_preimage, F.map_preimage]
  obtain ⟨h2, -⟩ := FinPAC.comp_ovee h e.inv
  obtain ⟨h3, -⟩ := FinPAC.ovee_comp h2 e.hom
  exact h3

include hsum in
theorem SumsCompatible.aux_ovee' (p q : SigmaEffectus.«I» (C := D) ⟶ SigmaEffectus.«I» (C := D))
    (h : Perp p q) (h' : Perp (F.preimage (e.hom ≫ p ≫ e.inv)) (F.preimage (e.hom ≫ q ≫ e.inv))) :
    F.preimage (e.hom ≫ ovee p q h ≫ e.inv) =
      ovee (F.preimage (e.hom ≫ p ≫ e.inv)) (F.preimage (e.hom ≫ q ≫ e.inv)) h' := by
  apply F.map_injective
  rw [hsum.map_ovee, F.map_preimage]
  obtain ⟨h2, e2⟩ := FinPAC.comp_ovee h e.inv
  obtain ⟨h3, e3⟩ := FinPAC.ovee_comp h2 e.hom
  rw [e2, e3]
  exact PCM.ovee_congr (F.map_preimage _).symm (F.map_preimage _).symm _ _

/-- A σ-effectus transported along a fully faithful sums-compatible functor
has isomorphic scalars. -/
theorem SumsCompatible.scal_emIso :
    letI := hsum.sigmaEffectus I' e hpres
    EMIso (Scal D') (Scal D) := by
  let _ := hsum.sigmaEffectus I' e hpres
  have t1 : (truth (effObj D') : I' ⟶ I') = 𝟙 I' := truth_effObj_eq_id
  have t2 : (truth (effObj D) : SigmaEffectus.«I» (C := D) ⟶ SigmaEffectus.«I» (C := D)) = 𝟙 _ :=
    truth_effObj_eq_id
  let φ : EffectMonoidHom (Scal D') (Scal D) :=
    { toFun := fun p => e.inv ≫ F.map (X := I') (Y := I') p ≫ e.hom
      perp_map := fun {p q} h => hsum.aux_perp I' e p q h
      ovee_map := fun {p q} h => hsum.aux_ovee I' e p q h _
      map_one := by
        show e.inv ≫ F.map (X := I') (Y := I') (truth (effObj D')) ≫ e.hom = truth (effObj D)
        rw [t1, t2, F.map_id, Category.id_comp, Iso.inv_hom_id]
        rfl
      map_mul := fun l m => by
        show e.inv ≫ F.map (X := I') (Y := I') (m ≫ l) ≫ e.hom =
          (e.inv ≫ F.map (X := I') (Y := I') m ≫ e.hom) ≫ (e.inv ≫ F.map (X := I') (Y := I') l ≫ e.hom)
        exact transport_aux_mul F e (X := I') m l }
  let ψ : EffectMonoidHom (Scal D) (Scal D') :=
    { toFun := fun q => F.preimage (X := I') (Y := I') (e.hom ≫ q ≫ e.inv)
      perp_map := fun {p q} h => hsum.aux_perp' I' e p q h
      ovee_map := fun {p q} h => hsum.aux_ovee' I' e p q h _
      map_one := by
        show F.preimage (X := I') (Y := I') (e.hom ≫ truth (effObj D) ≫ e.inv) = truth (effObj D')
        rw [t1, t2]
        apply F.map_injective
        rw [F.map_preimage, F.map_id]
        exact (congrArg (e.hom ≫ ·) (Category.id_comp e.inv)).trans e.hom_inv_id
      map_mul := fun l m => by
        show F.preimage (X := I') (Y := I') (e.hom ≫ (m ≫ l) ≫ e.inv) =
          F.preimage (X := I') (Y := I') (e.hom ≫ m ≫ e.inv) ≫ F.preimage (X := I') (Y := I') (e.hom ≫ l ≫ e.inv)
        exact transport_aux_mul' F e m l }
  refine ⟨φ, ψ, fun p => ?_, fun q => ?_⟩
  · exact transport_aux_inv F e (X := I') p
  · exact transport_aux_inv' F e q

end TransportScalars

/-- The composite of effect monoid homomorphisms. -/
def emHomComp {M N L : Type*} [EffectMonoid M] [EffectMonoid N] [EffectMonoid L]
    (g : EffectMonoidHom N L) (f : EffectMonoidHom M N) : EffectMonoidHom M L where
  toFun := g.toFun ∘ f.toFun
  perp_map h := g.perp_map (f.perp_map h)
  ovee_map h := by
    show g.toFun (f.toFun _) = _
    rw [f.ovee_map, g.ovee_map]
    rfl
  map_one := by show g.toFun (f.toFun 1) = 1; rw [f.map_one, g.map_one]
  map_mul a b := by show g.toFun (f.toFun (a * b)) = _; rw [f.map_mul, g.map_mul]; rfl

theorem EMIso.trans' {M N L : Type*} [EffectMonoid M] [EffectMonoid N] [EffectMonoid L]
    (h₁ : EMIso M N) (h₂ : EMIso N L) : EMIso M L := by
  obtain ⟨φ, ψ, h1, h2⟩ := h₁
  obtain ⟨φ', ψ', h1', h2'⟩ := h₂
  exact ⟨emHomComp φ' φ, emHomComp ψ ψ',
    fun a => by
      show ψ.toFun (ψ'.toFun (φ'.toFun (φ.toFun a))) = a
      rw [h1', h1],
    fun b => by
      show φ'.toFun (φ.toFun (ψ.toFun (ψ'.toFun b))) = b
      rw [h2, h2']⟩

/-! ## SIG 46: `sEA ≅ sEMod[{0,1}]` -/

section SIG46

/-- An object of `sEA`: a σ-effect algebra (SIG 17).  In universe `0`, that
of `sEMod[{0,1}]` (whose carriers live in the universe of `{0,1}`). -/
structure SEA : Type 1 where
  carrier : Type
  [ea : EffectAlgebra carrier]
  sigma : OmegaComplete carrier

attribute [instance] SEA.ea

namespace SEA

instance : CoeSort SEA Type := ⟨SEA.carrier⟩

/-- A morphism of `sEA`: a σ-additive map (additive, and preserving the
canonical countable sums). -/
@[ext]
structure Hom (E F : SEA) : Type where
  toFun : E.carrier → F.carrier
  additive : IsAdditive toFun
  sigma : IsSigmaAdditiveC toFun

instance : Category SEA where
  Hom := Hom
  id E := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ _ _ h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun J _ x s h => g.sigma J _ _ (f.sigma J x s h)⟩

@[simp] theorem id_toFun (E : SEA) : (𝟙 E : Hom E E).toFun = id := rfl
@[simp] theorem comp_toFun {E F G : SEA} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {E F : SEA} {f g : E ⟶ F} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

end SEA

/-- A family supported at one index has that value as canonical sum. -/
theorem isCSum_single {E : Type} [EffectAlgebra E] (hE : OmegaComplete E) {J : Type} [Countable J]
    (x : J → E) (i : J) (h : ∀ l, l ≠ i → x l = 0) : IsCSum x (x i) := by
  let _ := canonicalSigmaPAM hE
  have hz : (zero : E) = 0 := zero_eq_of_extends (canonicalSigmaPAM_extends hE)
  exact (canonical_sumsTo_iff hE x _).1 (sumsTo_single x i fun l hl => (h l hl).trans hz.symm)

/-- **SIG 46** (main.tex:1248, Example), objects: a σ-effect algebra is a
σ-effect `{0,1}`-module (`1·a = a`, `0·a = 0`). -/
theorem boolModule_isSigma (E : Type) [EffectAlgebra E] (hE : OmegaComplete E) :
    @IsSigmaEffectModule Bool _ E _ (effectModuleBool E) := by
  let _ := effectModuleBool E
  refine ⟨hE, fun r => ?_, fun a => ?_⟩
  · intro J _ x s hs
    cases r
    · simp only [effectModule_bool_smul, Bool.false_eq_true, ↓reduceIte]
      exact isCSum_const_zero
    · simpa only [effectModule_bool_smul, ↓reduceIte] using hs
  · intro J _ r s hs
    obtain ⟨hat, hne, hall⟩ := (bool_isCSum_iff r s).1 hs
    simp only [effectModule_bool_smul]
    by_cases hex : ∃ j, r j ≠ false
    · obtain ⟨j, hj⟩ := hex
      have hrj : r j = true := by simpa using hj
      have hs' : s = true := (hne j hj).trans hrj
      have := isCSum_single hE (fun l => if r l = true then a else 0) j (fun l hl => by
        have : r l = false := by
          by_contra h
          exact hl (hat l j h hj)
        simp [this])
      simpa [hrj, hs'] using this
    · push Not at hex
      have hs' : s = false := hall hex
      simp only [hex, hs', Bool.false_eq_true, ↓reduceIte]
      exact isCSum_const_zero

/-- **SIG 46** (main.tex:1248, Example): the functor `sEA → sEMod[{0,1}]`,
the identity on carriers and maps, each σ-effect algebra with its (unique)
`{0,1}`-action. -/
noncomputable def seaToSEMod : SEA ⥤ SEMod Bool where
  obj E := @SEMod.mk Bool _ E.carrier E.ea (effectModuleBool E.carrier)
    (boolModule_isSigma E.carrier E.sigma)
  map {_ _} f := ⟨f.toFun, f.additive, fun r a => by
      cases r
      · show f.toFun (if false = true then a else 0) = if false = true then f.toFun a else 0
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact f.additive.1
      · rfl, f.sigma⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance seaToSEMod_faithful : seaToSEMod.Faithful :=
  ⟨fun {_ _} _ _ h => SEA.hom_ext fun a => congrFun (congrArg SEMod.Hom.toFun h) a⟩

instance seaToSEMod_full : seaToSEMod.Full :=
  ⟨fun {_ _} g => ⟨⟨g.toFun, g.additive, g.sigma⟩, rfl⟩⟩

/-- The preimage of a σ-effect `{0,1}`-module. -/
def SEA.ofSEMod (X : SEMod Bool) : SEA := ⟨X.carrier, X.sigma.1⟩

theorem seaToSEMod_ofSEMod (X : SEMod Bool) : seaToSEMod.obj (SEA.ofSEMod X) = X := by
  rcases X with @⟨C, ea, m, hs⟩
  have := Theses.B.Eff.effectModule_bool_unique m
  subst this
  rfl

theorem seaToSEMod_obj_injective : Function.Injective seaToSEMod.obj := by
  intro E E' e
  rcases E with @⟨C, ea, h⟩
  rcases E' with @⟨C', ea', h'⟩
  simp only [seaToSEMod, SEMod.mk.injEq] at e
  obtain ⟨rfl, e2, -⟩ := e
  cases e2
  rfl

instance seaToSEMod_essSurj : seaToSEMod.EssSurj :=
  ⟨fun X => ⟨SEA.ofSEMod X, ⟨eqToIso (seaToSEMod_ofSEMod X)⟩⟩⟩

/-- **SIG 46** (main.tex:1248, Example): `sEA ≅ sEMod[{0,1}]`, an
isomorphism of categories: `seaToSEMod` is bijective on objects and fully
faithful (identity on carriers and on maps). -/
theorem sig46_iso : Function.Bijective seaToSEMod.obj ∧ seaToSEMod.Full ∧ seaToSEMod.Faithful :=
  ⟨⟨seaToSEMod_obj_injective, fun X => ⟨_, seaToSEMod_ofSEMod X⟩⟩, inferInstance, inferInstance⟩

instance seaToSEMod_isEquivalence : seaToSEMod.IsEquivalence := { }

/-- `sEMod[{0,1}]ᵒᵖ` with its σ-effectus structure (SIG 28/63). -/
noncomputable instance semodBool_sigmaEffectus : SigmaEffectus (SEMod Bool)ᵒᵖ :=
  SEMod.sigmaEffectus bool_isSigmaEffectMonoid

instance : HasCountableCoproducts SEAᵒᵖ :=
  ⟨fun _ _ => Adjunction.hasColimitsOfShape_of_equivalence seaToSEMod.op⟩

/-- The hom-sets of `sEAᵒᵖ` as σ-PAMs (transported along SIG 46). -/
noncomputable instance seaHomPAM (X Y : SEAᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  SigmaPAM.ofEquiv ((Functor.FullyFaithful.ofFullyFaithful seaToSEMod.op).homEquiv)

theorem sea_sumsCompatible : SumsCompatible seaToSEMod.op :=
  fun x s => SigmaPAM.ofEquiv_sumsTo_iff _ x s

/-- `{0,1}` as a σ-effect algebra: the unit object of `sEAᵒᵖ`. -/
def seaBool : SEA := { carrier := Bool, sigma := bool_isSigmaEffectMonoid.1 }

theorem seaToSEMod_bool : seaToSEMod.obj seaBool = SEMod.unit Bool bool_isSigmaEffectMonoid := by
  unfold SEMod.unit
  simp only [seaToSEMod, seaBool, SEMod.mk.injEq, heq_eq_eq, true_and]
  exact Theses.B.Eff.effectModule_bool_unique _

noncomputable def seaUnitIso :
    seaToSEMod.op.obj (op seaBool) ≅ SigmaEffectus.«I» (C := (SEMod Bool)ᵒᵖ) :=
  (eqToIso seaToSEMod_bool).op.symm

/-- **SIG 46** (main.tex:1249): "hence `sEAᵒᵖ` is a σ-effectus": the
σ-effectus structure transported along the isomorphism `sEA ≅ sEMod[{0,1}]`,
with unit `{0,1}`. -/
noncomputable instance sea_sigmaEffectus : SigmaEffectus SEAᵒᵖ :=
  sea_sumsCompatible.sigmaEffectus (op seaBool) seaUnitIso (fun _ _ => inferInstance)

/-- `sEAᵒᵖ → sEMod[{0,1}]ᵒᵖ` is a morphism of σ-effectuses. -/
noncomputable def seaMorphism : SigmaEffectusMorphism SEAᵒᵖ (SEMod Bool)ᵒᵖ :=
  sea_sumsCompatible.morphism (op seaBool) seaUnitIso (fun _ _ => inferInstance)

/-- **SIG 46** (main.tex:1250): `sEAᵒᵖ` has scalars `{0,1}`, so it is
deterministic (SIG 45's dichotomy, Boolean case). -/
theorem sea_scalars : EMIso (Scal SEAᵒᵖ) Bool :=
  EMIso.trans' (sea_sumsCompatible.scal_emIso (op seaBool) seaUnitIso (fun _ _ => inferInstance))
    (SEMod.sigmaEffectus_scalars bool_isSigmaEffectMonoid)

end SIG46

/-! ### SIG 46: states of `sEAᵒᵖ`, and the Kochen–Specker consequence -/

section SIG46States

/-- A map of `sEA` out of `{0,1}` is determined by its value at `1`. -/
theorem sea_hom_bool_ext {E : SEA} {f g : seaBool ⟶ E} (h : f.toFun true = g.toFun true) : f = g := by
  refine SEA.hom_ext fun r => ?_
  cases r
  · exact f.additive.1.trans g.additive.1.symm
  · exact h

/-- The truth predicate `1_X : X ⟶ {0,1}` of `sEAᵒᵖ` is the map `{0,1} → X`
with `1 ↦ 1`. -/
theorem sea_truth_apply (Z : SEAᵒᵖ) : (truth Z).unop.toFun true = 1 := by
  have h := congrArg (fun k => k.unop.toFun true)
    (seaToSEMod.op.map_preimage (SigmaEffectus.one (seaToSEMod.op.obj Z) ≫ seaUnitIso.inv))
  refine h.trans ?_
  show (SEMod.smulMap (seaToSEMod.obj Z.unop) bool_isSigmaEffectMonoid 1).toFun
    (seaUnitIso.inv.unop.toFun true) = 1
  have h1 : seaUnitIso.inv.unop.toFun true = true := SEMod.iso_hom_one seaUnitIso.symm.unop
  rw [h1]
  exact SEMod.smulMap_one_apply bool_isSigmaEffectMonoid _ 1

/-- **SIG 46** (main.tex:1268): the total maps of `sEAᵒᵖ` are the unital
σ-additive maps; in particular the states `St(E) = Tot(sEAᵒᵖ)({0,1}, E)` are
the unital σ-additive maps `E → {0,1}`. -/
theorem sea_isTotal_iff {X Y : SEAᵒᵖ} (f : X ⟶ Y) : IsTotal f ↔ f.unop.toFun 1 = 1 := by
  show f ≫ truth Y = truth X ↔ _
  constructor
  · intro h
    have := congrArg (fun k : X ⟶ op seaBool => k.unop.toFun true) h
    change f.unop.toFun ((truth Y).unop.toFun true) = (truth X).unop.toFun true at this
    rwa [sea_truth_apply, sea_truth_apply] at this
  · intro h
    apply Quiver.Hom.unop_inj
    refine sea_hom_bool_ext ?_
    change f.unop.toFun ((truth Y).unop.toFun true) = (truth X).unop.toFun true
    rw [sea_truth_apply, sea_truth_apply, h]

/-- A substate `ω : {0,1} ⟶ E` of `sEAᵒᵖ` (a σ-additive map `E → {0,1}`)
with `ω(1) = 0` is zero. -/
theorem sea_substate_zero {E : SEA} (ω : E ⟶ seaBool) (h : (ω.toFun 1 : Bool) = false)
    (a : E.carrier) : (ω.toFun a : Bool) = false := by
  obtain ⟨c, hc, e⟩ := ea_le_one a
  obtain ⟨h', e'⟩ := ω.additive.2 hc
  have e3 : ((ω.toFun a : Bool) || (ω.toFun c : Bool)) = false := by
    rw [← h]; exact e'.trans (congrArg ω.toFun e)
  exact (Bool.or_eq_false_iff.1 e3).1

/-- **SIG 46** (main.tex:1271), the general step: if `P → E` is a unital
map of `sEA` (e.g. the inclusion of a σ-effect subalgebra) and `P` has no
states, neither has `E`, and every substate of `E` is zero ("`E` is
operationally equivalent to the empty system"). -/
theorem sea_no_states_of_sub {P E : SEA} (ι : P ⟶ E) (hι : ι.toFun 1 = 1)
    (hP : ∀ ω : P ⟶ seaBool, ω.toFun 1 ≠ true) :
    (∀ ω : E ⟶ seaBool, ω.toFun 1 ≠ true) ∧
      ∀ (ω : E ⟶ seaBool) (a : E.carrier), (ω.toFun a : Bool) = false := by
  have h1 : ∀ ω : E ⟶ seaBool, ω.toFun 1 ≠ true := fun ω hω =>
    hP (ι ≫ ω) (by show ω.toFun (ι.toFun 1) = true; rw [hι]; exact hω)
  exact ⟨h1, fun ω a => sea_substate_zero ω (Bool.eq_false_iff.mpr (h1 ω)) a⟩

/-! #### The projections of a von Neumann algebra as a σ-effect algebra -/

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Theses.VonNeumannAlgebra A]

variable (A) in
/-- The projections `P(𝒜) ⊆ [0,1]_𝒜` of a von Neumann algebra. -/
abbrev Proj : Type u := {a : Theses.effects A // IsStarProjection (a : A)}

theorem proj_add {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p + q ≤ 1) :
    IsStarProjection (p + q) :=
  ((Theses.A.VN.orthogonal_tuple_of_projections_1 p q hp hq).out 3 5).mp h

/-- `P(𝒜)` is a sub-effect algebra of `[0,1]_𝒜`: `p ⊥ q` iff `p + q ≤ 1`, and
then `p + q` is a projection; `p^⊥ = 1 - p`. -/
noncomputable instance projEffectAlgebra : EffectAlgebra (Proj A) where
  zero := ⟨0, IsStarProjection.zero A⟩
  one := ⟨1, IsStarProjection.one A⟩
  Perp p q := Perp p.1 q.1
  ovee p q h := ⟨ovee p.1 q.1 h, proj_add p.2 q.2 h⟩
  orth p := ⟨orth p.1, p.2.one_sub⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp (M := Theses.effects A) hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp (M := Theses.effects A) hab h
  ovee_assoc hab h := Subtype.ext (PCM.ovee_assoc (M := Theses.effects A) hab h)
  zero_perp a := PCM.zero_perp a.1
  zero_ovee a := Subtype.ext (PCM.zero_ovee a.1)
  perp_orth a := EffectAlgebra.perp_orth a.1
  ovee_orth a := Subtype.ext (EffectAlgebra.ovee_orth a.1)
  orth_unique h e := Subtype.ext (EffectAlgebra.orth_unique (E := Theses.effects A) h
    (congrArg Subtype.val e))
  eq_zero_of_perp_one h := Subtype.ext (EffectAlgebra.eq_zero_of_perp_one (E := Theses.effects A) h)

theorem proj_val_ovee {p q : Proj A} (h : Perp p q) :
    ((ovee p q h : Proj A).1 : A) = (p.1 : A) + q.1 := rfl

/-- The order of `P(𝒜)` is the order of `𝒜`. -/
theorem proj_le_iff (p q : Proj A) : p ≼ q ↔ (p.1 : A) ≤ q.1 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact le_add_of_nonneg_right c.1.2.1
  · intro h
    have hr : (p.1 : A) + (1 - q.1) ≤ 1 := by
      have : (p.1 : A) + (1 - q.1) = 1 - (q.1 - p.1) := by abel
      rw [this]; exact sub_le_self _ (sub_nonneg.mpr h)
    have hpr : IsStarProjection ((p.1 : A) + (1 - q.1)) := proj_add p.2 q.2.one_sub hr
    have hc : IsStarProjection ((q.1 : A) - p.1) := by
      have := hpr.one_sub
      rwa [show (1 : A) - ((p.1 : A) + (1 - q.1)) = q.1 - p.1 by abel] at this
    let c : Proj A := ⟨⟨(q.1 : A) - p.1, sub_nonneg.mpr h, (sub_le_self _ p.1.2.1).trans q.1.2.2⟩, hc⟩
    refine ⟨c, ?_, Subtype.ext (Subtype.ext ?_)⟩
    · show (p.1 : A) + (q.1 - p.1) ≤ 1
      rw [add_sub_cancel]; exact q.1.2.2
    · show (p.1 : A) + (q.1 - p.1) = q.1
      rw [add_sub_cancel]

/-- Finite sums in `P(𝒜)` are sums in `𝒜`. -/
theorem isSumOf_proj_iff (l : List (Proj A)) (t : Proj A) :
    PCM.IsSumOf l t → ((t.1 : A) = (l.map fun p => (p.1 : A)).sum) := by
  intro h
  induction h with
  | nil => rfl
  | cons hl h ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    rfl

/-- **SIG 46** (main.tex:1261): the projections form a σ-effect algebra
(`P(𝒜)` is ω-complete: the supremum of an increasing sequence of projections
is a projection, tree **56XIV**). -/
theorem proj_omegaComplete : OmegaComplete (Proj A) := by
  intro a ha
  have hmono : Monotone fun n => (a n).1.1 :=
    monotone_nat_of_le_succ fun n => (proj_le_iff _ _).1 (ha n)
  obtain ⟨s, hs, -, h0, h1⟩ := eff_exists_lub (fun n => (a n).1.1) hmono
    (fun n => (a n).1.2.1) (fun n => (a n).1.2.2)
  have hsp : IsStarProjection s := Theses.A.VN.vna_directed_supremum_projections
    (Set.range fun n => (a n).1.1) s (by rintro _ ⟨n, rfl⟩; exact (a n).2)
    (Set.range_nonempty _) (directedOn_range.2 hmono.directed_le) hs
  refine ⟨⟨⟨s, h0, h1⟩, hsp⟩, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (proj_le_iff _ _).2 (hs.1 ⟨n, rfl⟩)
  · intro c hc
    refine (proj_le_iff _ _).2 (hs.2 ?_)
    rintro _ ⟨n, rfl⟩
    exact (proj_le_iff _ _).1 (hc _ ⟨n, rfl⟩)

/-- Canonical countable sums in `P(𝒜)` are those of `[0,1]_𝒜`. -/
theorem proj_isCSum {J : Type} {x : J → Proj A} {s : Proj A} (h : IsCSum x s) :
    IsCSum (fun j => (x j).1) s.1 := by
  have hfin : ∀ F : Finset J, ∃ t : Proj A, FinSum x F t ∧
      (t.1 : A) = ∑ j ∈ F, ((x j).1 : A) := fun F => by
    obtain ⟨t, ht⟩ := h.1 F
    refine ⟨t, ht, (isSumOf_proj_iff _ t ht).trans ?_⟩
    rw [List.map_map]
    exact Finset.sum_map_toList F _
  have hmono : Monotone fun F : Finset J => ∑ j ∈ F, ((x j).1 : A) := fun F G hFG =>
    Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ => (x j).1.2.1
  have hb : ∀ F : Finset J, ∑ j ∈ F, ((x j).1 : A) ≤ 1 := fun F => by
    obtain ⟨t, -, ht⟩ := hfin F; rw [← ht]; exact t.1.2.2
  refine (isCSum_eff_iff _ _).2 ⟨hb, ?_⟩
  obtain ⟨w, hw, -, h0, h1⟩ := eff_exists_lub _ hmono
    (fun F => Finset.sum_nonneg fun j _ => (x j).1.2.1) hb
  have hwp : IsStarProjection w := by
    refine Theses.A.VN.vna_directed_supremum_projections
      (Set.range fun F : Finset J => ∑ j ∈ F, ((x j).1 : A)) w ?_ (Set.range_nonempty _)
      (directedOn_range.2 hmono.directed_le) hw
    rintro _ ⟨F, rfl⟩
    obtain ⟨t, -, ht⟩ := hfin F
    show IsStarProjection (∑ j ∈ F, ((x j).1 : A))
    rw [← ht]; exact t.2
  let w' : Proj A := ⟨⟨w, h0, h1⟩, hwp⟩
  have hsw : s = w' := by
    refine eabasics_le_antisymm (h.2.2 _ ?_) ((proj_le_iff w' s).2 (hw.2 ?_))
    · rintro t ⟨F, hF⟩
      obtain ⟨t', ht', e⟩ := hfin F
      rw [finSum_unique hF ht']
      refine (proj_le_iff t' w').2 ?_
      show (t'.1 : A) ≤ w
      rw [e]; exact hw.1 ⟨F, rfl⟩
    · rintro _ ⟨F, rfl⟩
      obtain ⟨t, ht, e⟩ := hfin F
      show ∑ j ∈ F, ((x j).1 : A) ≤ (s.1 : A)
      rw [← e]
      exact (proj_le_iff _ _).1 (h.2.1 t ⟨F, ht⟩)
  rw [hsw]
  exact hw

variable (A) in
/-- `[0,1]_𝒜` as an object of `sEA` (for `𝒜 : Type`). -/
noncomputable def seaEffects (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : SEA := ⟨Theses.effects A, effects_omegaComplete A⟩

/-- `P(𝒜)` as an object of `sEA`. -/
noncomputable def seaProj (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : SEA := ⟨Proj A, proj_omegaComplete⟩

/-- **SIG 46** (main.tex:1261): `P(𝒜)` is a σ-effect subalgebra of
`[0,1]_𝒜`: the inclusion is a unital map of `sEA`. -/
noncomputable def projIncl (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : seaProj A ⟶ seaEffects A where
  toFun p := p.1
  additive := ⟨rfl, fun h => ⟨h, rfl⟩⟩
  sigma _ _ _ _ h := proj_isCSum h

end SIG46States

/-- The Kochen–Specker theorem (not in Mathlib; cited by the print,
[KS67]), as a named hypothesis: for a Hilbert space `H` with `dim H > 2`
there is no unital σ-additive map `P(H) → {0,1}`, i.e. `St(P(H)) = ∅` in
`sEAᵒᵖ`. -/
def KochenSpecker (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Prop :=
  2 < Module.rank ℂ H → ∀ ω : seaProj (H →L[ℂ] H) ⟶ seaBool, ω.toFun 1 ≠ true

/-- **SIG 46** (main.tex:1257–1277, Example): for a Hilbert space `H` with
`dim H > 2`, `E = [0,1]_{B(H)}` is a σ-effect algebra with the σ-effect
subalgebra `P(H)` of projections (`projIncl`); given the Kochen–Specker
theorem (`KochenSpecker H`, a named hypothesis), neither has states — there
is no total map `{0,1} ⟶ P(H)` or `{0,1} ⟶ E` in `sEAᵒᵖ` — and every
substate of `E` is zero, so `E` is operationally equivalent to the empty
system. -/
theorem sig46_kochenSpecker (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hKS : KochenSpecker H) (hdim : 2 < Module.rank ℂ H) :
    (∀ ω : op seaBool ⟶ op (seaProj (H →L[ℂ] H)), ¬ IsTotal ω) ∧
      (∀ ω : op seaBool ⟶ op (seaEffects (H →L[ℂ] H)), ¬ IsTotal ω) ∧
      ∀ (ω : op seaBool ⟶ op (seaEffects (H →L[ℂ] H))) (a : Theses.effects (H →L[ℂ] H)),
        ω.unop.toFun a = false := by
  have hP := hKS hdim
  obtain ⟨hE, hz⟩ := sea_no_states_of_sub (projIncl (H →L[ℂ] H)) rfl hP
  refine ⟨fun ω h => hP ω.unop ((sea_isTotal_iff ω).1 h), fun ω h => hE ω.unop ((sea_isTotal_iff ω).1 h),
    fun ω a => hz ω.unop a⟩

/-! ## SIG 15 as printed: normal positive subunital maps

The print's `W*` has subunital normal *positive* maps.  The construction
above, for completely positive maps, is repeated here for positive maps; the
two differences are the existence of ultraweak sums (`exists_pos_uwsum`, the
tree's `exists_ncp_uwsum` without the complete-positivity clause) and the
tupling into `⊕_j 𝒜_j` (`pos_products`, bounded by Russo–Dye). -/

section PositiveMaps

open Filter Topology
open Theses.A.VN (UWTendsto)

variable {A B C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A **normal positive subunital map** (npsu-map): the morphisms of the
print's `W*`. -/
structure NPSUMap (A B : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] extends A →ₚ[ℂ] B where
  normal : Theses.PreservesDirSups ⇑toPositiveLinearMap
  subunital : toPositiveLinearMap 1 ≤ 1

namespace NPSUMap

noncomputable instance : FunLike (NPSUMap A B) A B where
  coe f := f.toPositiveLinearMap
  coe_injective f g h := by
    obtain ⟨f, _, _⟩ := f
    obtain ⟨g, _, _⟩ := g
    congr
    exact DFunLike.coe_injective h

theorem ext' {f g : NPSUMap A B} (h : ∀ a, f a = g a) : f = g := DFunLike.coe_injective (funext h)

theorem mono (f : NPSUMap A B) {a b : A} (h : a ≤ b) : f a ≤ f b := f.monotone' h

theorem map_add (f : NPSUMap A B) (a b : A) : f (a + b) = f a + f b :=
  _root_.map_add f.toPositiveLinearMap a b

theorem map_smul (f : NPSUMap A B) (c : ℂ) (a : A) : f (c • a) = c • f a :=
  _root_.map_smul f.toPositiveLinearMap c a

theorem map_zero (f : NPSUMap A B) : f 0 = 0 := _root_.map_zero f.toPositiveLinearMap

theorem map_sum (f : NPSUMap A B) {ι : Type*} (s : Finset ι) (x : ι → A) :
    f (∑ i ∈ s, x i) = ∑ i ∈ s, f (x i) := _root_.map_sum f.toPositiveLinearMap x s

theorem nonneg (f : NPSUMap A B) {a : A} (h : 0 ≤ a) : 0 ≤ f a := by
  have := f.mono h; rwa [f.map_zero] at this

theorem one_nonneg (f : NPSUMap A B) : 0 ≤ f 1 := f.nonneg zero_le_one

theorem mem_effects (f : NPSUMap A B) {b : A} (hb : b ∈ Theses.effects A) :
    f b ∈ Theses.effects B :=
  ⟨f.nonneg hb.1, (f.mono hb.2).trans f.subunital⟩

theorem isPositiveMap (f : A →ₚ[ℂ] B) : Theses.A.CStar.IsPositiveMap f.toLinearMap := fun a ha => by
  have := OrderHomClass.mono f ha
  rw [_root_.map_zero] at this
  exact this

theorem sa (f : A →ₚ[ℂ] B) {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (f a) := by
  have := Theses.A.CStar.cstar_p_implies_i f.toLinearMap (isPositiveMap f) a
  rw [ha.star_eq] at this
  exact this.symm

/-- The identity npsu-map. -/
noncomputable def id (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    NPSUMap A A :=
  ⟨PositiveLinearMap.id ℂ A, fun D s hne _ h => by
    simpa using Theses.A.Proc.isLUB_val_of_isLUB hne h, le_rfl⟩

/-- Composition of npsu-maps (diagrammatic order). -/
noncomputable def comp (f : NPSUMap A B) (g : NPSUMap B C) : NPSUMap A C :=
  ⟨g.toPositiveLinearMap.comp f.toPositiveLinearMap,
    preservesDirSups_comp' (f := ⇑f.toPositiveLinearMap) (g := ⇑g.toPositiveLinearMap) f.normal
      (fun a => sa f.toPositiveLinearMap a.2) g.normal,
    (g.mono f.subunital).trans g.subunital⟩

@[simp] theorem id_apply (a : A) : NPSUMap.id A a = a := rfl
@[simp] theorem comp_apply (f : NPSUMap A B) (g : NPSUMap B C) (a : A) : f.comp g a = g (f a) := rfl

/-- The npsu-map underlying an ncpsu-map. -/
noncomputable def ofNCPSU (f : Theses.NCPSUMap A B) : NPSUMap A B :=
  ⟨{ toLinearMap := ncpLin f.toNCPMap
     monotone' := fun _ _ h => OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap h },
    f.toNCPMap.preservesDirSups', f.subunital'⟩

@[simp] theorem ofNCPSU_apply (f : Theses.NCPSUMap A B) (a : A) : ofNCPSU f a = f.toNCPMap a := rfl

/-- An npsu-map killing `1` is zero. -/
theorem eq_zero_of_one (f : NPSUMap A B) (h1 : f 1 = 0) (a : A) : f a = 0 := by
  refine linear_eq_zero_of_nonneg (f := f.toLinearMap) (fun c hc => ?_) a
  obtain ⟨n, e, he, rfl⟩ := exists_effect_smul hc
  have h0 : f e = 0 := le_antisymm (by rw [← h1]; exact f.mono he.2) (f.nonneg he.1)
  show f ((n : ℂ) • e) = 0
  rw [f.map_smul, h0, smul_zero]

/-- npsu-maps agreeing on effects are equal. -/
theorem ext_effects {f g : NPSUMap A B} (h : ∀ b ∈ Theses.effects A, f b = g b) : f = g := by
  refine ext' fun a => ?_
  have := linear_eq_zero_of_nonneg (f := f.toLinearMap - g.toLinearMap) (fun c hc => by
    obtain ⟨n, e, he, rfl⟩ := exists_effect_smul hc
    show f ((n : ℂ) • e) - g ((n : ℂ) • e) = 0
    rw [f.map_smul, g.map_smul, h e he, sub_self]) a
  exact sub_eq_zero.mp this

/-- An npsu-map out of the scalars is determined by its value at `1`. -/
theorem scal_ext {f g : NPSUMap (ULift.{u} ℂ) A} (h : f 1 = g 1) : f = g := by
  refine ext' fun z => ?_
  have hz : (z.down • (1 : ULift.{u} ℂ)) = z := Theses.A.VN.CU.down_injective (by simp)
  rw [← hz, f.map_smul, g.map_smul, h]

end NPSUMap

/-! ### The category `W*` (von Neumann algebras, npsu-maps) -/

/-- The objects of `W*`: von Neumann algebras (the morphisms: npsu-maps). -/
structure WStarPSU : Type (u + 1) where
  of ::
  base : WStar.{u}

noncomputable instance : Category.{u} WStarPSU.{u} where
  Hom A B := NPSUMap A.base B.base
  id A := NPSUMap.id A.base
  comp f g := NPSUMap.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A morphism of `W*` as an npsu-map. -/
abbrev ap {X Y : WStarPSU.{u}} (f : X ⟶ Y) : NPSUMap X.base Y.base := f

theorem ap_comp {X Y Z : WStarPSU.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X.base) :
    ap (f ≫ g) a = ap g (ap f a) := rfl

theorem ap_id {X : WStarPSU.{u}} (a : X.base) : ap (𝟙 X) a = a := rfl

theorem psuop_comp_apply {X Y Z : WStarPSU.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Z.unop.base) :
    ap (f ≫ g).unop a = ap f.unop (ap g.unop a) := rfl

theorem psuop_hom_ext {X Y : WStarPSU.{u}ᵒᵖ} {f g : X ⟶ Y} (h : ∀ a, ap f.unop a = ap g.unop a) :
    f = g :=
  Quiver.Hom.unop_inj (NPSUMap.ext' h)

/-! ### Ultraweak sums of npsu-maps -/

section UWSum

open Theses Theses.A.VN

variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T] [VonNeumannAlgebra T]
  {A' : Type u} [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A'] [VonNeumannAlgebra A']
  {ι : Type*}

/-- The finite partial sum `∑_{i∈F} gᵢ` of positive maps. -/
noncomputable def posPartSum (g : ι → (T →ₚ[ℂ] A')) (F : Finset ι) : T →ₚ[ℂ] A' where
  toFun b := ∑ i ∈ F, g i b
  map_add' b b' := by simp only [_root_.map_add, Finset.sum_add_distrib]
  map_smul' c b := by simp only [_root_.map_smul, Finset.smul_sum, RingHom.id_apply]
  monotone' b b' hb := Finset.sum_le_sum fun i _ => OrderHomClass.mono (g i) hb

theorem posPartSum_normal (g : ι → (T →ₚ[ℂ] A')) (hg : ∀ i, PreservesDirSups ⇑(g i))
    (F : Finset ι) : PreservesDirSups ⇑(posPartSum g F) := by
  refine ((p_uwcont (posPartSum g F)).out 0 2).mp ?_
  let _ : TopologicalSpace T := ultraweak _
  refine continuous_ultraweak_of_forall _ fun ω => ?_
  have h : (fun b => (ω (posPartSum g F b) : ℂ)) = fun b => ∑ i ∈ F, (ω (g i b) : ℂ) := by
    funext b
    exact _root_.map_sum ω.toPositiveLinearMap _ F
  rw [h]
  refine continuous_finsetSum F fun i _ => ?_
  exact @Continuous.comp _ _ _ (ultraweak _) (ultraweak A') _ _ _
    (continuous_ultraweak_npFunctional ω) (((p_uwcont (g i)).out 2 0).mp (hg i))

/-- The ultraweak sum of a family of normal positive maps whose partial sums
are bounded at `1` (the tree's `exists_ncp_uwsum`, **96III**, for positive
maps; same proof without the complete-positivity clause). -/
theorem exists_pos_uwsum (g : ι → (T →ₚ[ℂ] A')) (hg : ∀ i, PreservesDirSups ⇑(g i)) (b₀ : A')
    (hb : ∀ F : Finset ι, ∑ i ∈ F, g i 1 ≤ b₀) :
    ∃ L : T →ₚ[ℂ] A', PreservesDirSups ⇑L ∧
      ∀ z, UWTendsto (fun F : Finset ι => ∑ i ∈ F, g i z) atTop (L z) := by
  classical
  let _ : TopologicalSpace A' := ultraweak A'
  have : T2Space A' := vn_positive_basic_1.1
  have : IsTopologicalAddGroup A' := ultraweak_isTopologicalAddGroup
  have : ContinuousSMul ℂ A' := Theses.A.Proc.ultraweak_continuousSMul_complex
  set S := posPartSum g with hSdef
  have hS1 : ∀ F, S F 1 ≤ b₀ := hb
  have hpos : ∀ b : T, 0 ≤ b →
      ∃ s, IsLUB (Set.range fun F => S F b) s ∧ UWTendsto (fun F => S F b) atTop s := by
    intro b hb0
    have hmono : Monotone fun F => S F b := by
      intro F G hFG
      change S F b ≤ S G b
      show ∑ i ∈ F, g i b ≤ ∑ i ∈ G, g i b
      rw [← Finset.sum_sdiff hFG]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => NPSUMap.isPositiveMap (g i) b hb0)
    have hbd : ∀ F, S F b ≤ ‖b‖ • b₀ := by
      intro F
      have h1 : S F b ≤ S F (algebraMap ℝ T ‖b‖) :=
        (S F).monotone' (IsSelfAdjoint.of_nonneg hb0).le_algebraMap_norm_self
      have h2 : S F (algebraMap ℝ T ‖b‖) = ‖b‖ • S F 1 := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, _root_.map_smul, Complex.coe_smul]
      rw [h2] at h1
      refine h1.trans (sub_nonneg.mp ?_)
      rw [← smul_sub]
      exact smul_nonneg (norm_nonneg b) (sub_nonneg.mpr (hS1 F))
    have hnn : ∀ F, 0 ≤ S F b := fun F => by
      have := OrderHomClass.mono (S F) hb0
      rwa [_root_.map_zero] at this
    exact Theses.B.Dils.wit_uwTendsto_of_monotone _ hmono
      (fun F => IsSelfAdjoint.of_nonneg (hnn F)) hbd
  have hconv : ∀ b : T, ∃ s, UWTendsto (fun F => S F b) atTop s := by
    refine Theses.B.Dils.wit_nonneg_induction _ (fun b hb => (hpos b hb).imp fun s hs => hs.2) ?_ ?_
    · rintro b b' ⟨s, hs⟩ ⟨s', hs'⟩
      exact ⟨s + s', (hs.add hs').congr fun F => (_root_.map_add (S F) b b').symm⟩
    · rintro c b ⟨s, hs⟩
      exact ⟨c • s, (hs.const_smul c).congr fun F => (_root_.map_smul (S F) c b).symm⟩
  choose L hL using hconv
  have hLadd : ∀ b b', L (b + b') = L b + L b' := fun b b' =>
    uwTendsto_unique (hL (b + b'))
      ((hL b).add (hL b') |>.congr fun F => (_root_.map_add (S F) b b').symm)
  have hLsmul : ∀ (c : ℂ) b, L (c • b) = c • L b := fun c b =>
    uwTendsto_unique (hL (c • b))
      ((hL b).const_smul c |>.congr fun F => (_root_.map_smul (S F) c b).symm)
  set Ll : T →ₗ[ℂ] A' := { toFun := L, map_add' := hLadd, map_smul' := hLsmul }
  have hLl : ∀ b, UWTendsto (fun F => S F b) atTop (Ll b) := hL
  have htail : ∀ F (b : T), 0 ≤ b → S F b ≤ L b := by
    intro F b hb0
    obtain ⟨s, hs, hlim⟩ := hpos b hb0
    rw [uwTendsto_unique (hL b) hlim]
    exact hs.1 ⟨F, rfl⟩
  have hunif : ∀ ω : NPFunctional A', ∀ ε > (0 : ℝ),
      ∀ᶠ F in atTop, ∀ p ∈ effects T, ‖ω (S F p) - ω (Ll p)‖ ≤ ε := by
    intro ω ε hε
    have h1 : Tendsto (fun F => ‖ω (Ll 1) - ω (S F 1)‖) atTop (𝓝 0) := by
      change Tendsto (fun F => ‖ω (L 1) - ω (S F 1)‖) atTop (𝓝 0)
      have := ((uwTendsto_iff _ _ _).mp (hL 1) ω)
      have h2 := (tendsto_const_nhds (x := ω (L 1))).sub this
      rw [sub_self] at h2
      simpa using h2.norm
    filter_upwards [(tendsto_order.1 h1).2 ε hε] with F hF p hp
    have hp0 : 0 ≤ Ll p - S F p := sub_nonneg.mpr (htail F p hp.1)
    have hp1 : Ll p - S F p ≤ Ll 1 - S F 1 := by
      have := htail F (1 - p) (sub_nonneg.mpr hp.2)
      change S F (1 - p) ≤ Ll (1 - p) at this
      rw [_root_.map_sub, _root_.map_sub] at this
      rw [← sub_nonneg] at this ⊢
      convert this using 1
      change Ll 1 - S F 1 - (Ll p - S F p) = Ll 1 - Ll p - (S F 1 - S F p)
      abel
    have hω0 := npFunctional_nonneg ω hp0
    have hω1 := npFunctional_mono ω hp1
    rw [npFunctional_sub] at hω0 hω1
    rw [npFunctional_sub] at hω1
    rw [← norm_neg, neg_sub]
    exact (Theses.B.Dils.wit_norm_le_of_le hω0 hω1).trans hF.le
  have hn := Theses.A.Proc.ncp_uwlim_2 atTop S Ll hLl (fun F => posPartSum_normal g hg F) hunif
  refine ⟨⟨Ll, fun a b hab => ?_⟩, hn, hL⟩
  -- positivity: `L b - L a` is the ultraweak limit of the positive `S F (b - a)`
  obtain ⟨s, hs, hlim⟩ := hpos (b - a) (sub_nonneg.mpr hab)
  have e : L (b - a) = s := uwTendsto_unique (hL (b - a)) hlim
  have hs0 : 0 ≤ s := by
    have hnn : 0 ≤ S ∅ (b - a) := by
      show (0 : A') ≤ ∑ i ∈ (∅ : Finset ι), g i (b - a)
      rw [Finset.sum_empty]
    exact hnn.trans (hs.1 ⟨∅, rfl⟩)
  have : L (b - a) = L b - L a := by
    have := hLadd (b - a) a
    rw [sub_add_cancel] at this
    rw [this]; abel
  show L a ≤ L b
  rw [← sub_nonneg, ← this, e]
  exact hs0

end UWSum

end PositiveMaps

/-! ### The σ-PAM of ultraweak sums on `W*ᵒᵖ(X, Y)` -/

section PSUHoms

open Theses.A.VN (UWTendsto)

variable {X Y : WStarPSU.{u}ᵒᵖ}

/-- Evaluation of `f : X ⟶ Y` of `W*ᵒᵖ` (an npsu-map `Y → X`) at the effects
of `Y`. -/
noncomputable def pvnEv (f : X ⟶ Y) (b : Theses.effects Y.unop.base) : Theses.effects X.unop.base :=
  ⟨ap f.unop b, (ap f.unop).mem_effects b.2⟩

theorem pvn_exists_sum {J : Type} (f : J → (X ⟶ Y))
    (hb : ∀ F : Finset J, ∑ j ∈ F, ap (f j).unop 1 ≤ 1) :
    ∃ g : X ⟶ Y, (∀ b, UWTendsto (fun F : Finset J => ∑ j ∈ F, ap (f j).unop b)
        Filter.atTop (ap g.unop b)) ∧
      ∀ b ∈ Theses.effects Y.unop.base,
        IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, ap (f j).unop b) (ap g.unop b) := by
  classical
  obtain ⟨L, hLn, hL⟩ := exists_pos_uwsum (fun j => (ap (f j).unop).toPositiveLinearMap)
    (fun j => (ap (f j).unop).normal) 1 hb
  have hlub : ∀ b ∈ Theses.effects Y.unop.base,
      IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, ap (f j).unop b) (L b) := by
    intro b hbe
    have hmono : Monotone fun F : Finset J => ∑ j ∈ F, ap (f j).unop b := fun F G hFG =>
      Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ => (ap (f j).unop).nonneg hbe.1
    obtain ⟨s, hs, hlim, -, -⟩ := eff_exists_lub _ hmono
      (fun F => Finset.sum_nonneg fun j _ => (ap (f j).unop).nonneg hbe.1)
      (fun F => (Finset.sum_le_sum fun j _ => (ap (f j).unop).mono hbe.2).trans (hb F))
    rwa [Theses.A.VN.uwTendsto_unique (hL b) hlim]
  have hsu : L 1 ≤ 1 :=
    (hlub 1 ⟨zero_le_one, le_rfl⟩).2 (by rintro _ ⟨F, rfl⟩; exact hb F)
  exact ⟨Quiver.Hom.op (show Y.unop ⟶ X.unop from ⟨L, hLn, hsu⟩), hL, hlub⟩

theorem pvn_pSumsTo_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) (g : X ⟶ Y) :
    PSumsTo pvnEv f g ↔ (∀ F : Finset J, ∑ j ∈ F, ap (f j).unop 1 ≤ 1) ∧
      ∀ b ∈ Theses.effects Y.unop.base,
        IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, ap (f j).unop b) (ap g.unop b) := by
  constructor
  · intro h
    exact ⟨((eff_sumsTo_iff _ _).1 (h 1)).1, fun b hb => ((eff_sumsTo_iff _ _).1 (h ⟨b, hb⟩)).2⟩
  · rintro ⟨hb, hlub⟩ b
    refine (eff_sumsTo_iff _ _).2 ⟨fun F => ?_, hlub b b.2⟩
    exact (Finset.sum_le_sum fun j _ => (ap (f j).unop).mono b.2.2).trans (hb F)

theorem pvnHomData (X Y : WStarPSU.{u}ᵒᵖ) : PointwiseData (pvnEv (X := X) (Y := Y)) where
  inj f g h := Quiver.Hom.unop_inj (NPSUMap.ext_effects fun b hb =>
    congrArg Subtype.val (congrFun h ⟨b, hb⟩))
  nonempty := ⟨Quiver.Hom.op (show Y.unop ⟶ X.unop from NPSUMap.ofNCPSU (wZeroSU _ _))⟩
  sub f P := by
    rintro ⟨g, hg⟩
    have hb := ((pvn_pSumsTo_iff f g).1 hg).1
    have hb' : ∀ F : Finset {j // P j}, ∑ j ∈ F, ap (f j.1).unop 1 ≤ 1 := fun F => by
      have := hb (F.map (Function.Embedding.subtype P))
      rwa [Finset.sum_map] at this
    obtain ⟨g', -, hlub⟩ := pvn_exists_sum (fun j : {j // P j} => f j.1) hb'
    exact ⟨g', (pvn_pSumsTo_iff _ _).2 ⟨hb', hlub⟩⟩
  lim f h := by
    have hb : ∀ F : Finset _, ∑ j ∈ F, ap (f j).unop 1 ≤ 1 := by
      intro F
      obtain ⟨g, hg⟩ := h F
      have := ((pvn_pSumsTo_iff _ g).1 hg).1 Finset.univ
      rwa [Finset.sum_coe_sort F (fun j => ap (f j).unop 1)] at this
    obtain ⟨g, -, hlub⟩ := pvn_exists_sum f hb
    exact ⟨g, (pvn_pSumsTo_iff f g).2 ⟨hb, hlub⟩⟩

/-- **SIG 15** (`ex:wstar`, main.tex:554): the σ-PAM on the hom-sets of
`W*ᵒᵖ`: ultraweak sums of npsu-maps. -/
noncomputable instance pvnHomSigmaPAM (X Y : WStarPSU.{u}ᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  pointwiseSigmaPAM (pvnHomData X Y)

/-- **SIG 15** (`ex:wstar`, main.tex:554, Example), the sums as printed: a
countable family `f_j : 𝔄 → 𝔅` in `W*ᵒᵖ` (npsu-maps `𝔅 → 𝔄`) sums to `g`
iff `∑_{j∈F} f_j(1) ≤ 1` for every finite `F` and `g(b) = ∑_j f_j(b)`, the
sum converging ultraweakly. -/
theorem pvn_sumsTo_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) (g : X ⟶ Y) :
    SumsTo f g ↔ (∀ F : Finset J, ∑ j ∈ F, ap (f j).unop 1 ≤ 1) ∧
      ∀ b, UWTendsto (fun F : Finset J => ∑ j ∈ F, ap (f j).unop b) Filter.atTop (ap g.unop b) := by
  rw [pointwise_sumsTo_iff, pvn_pSumsTo_iff]
  constructor
  · rintro ⟨hb, hlub⟩
    obtain ⟨g', hg', hlub'⟩ := pvn_exists_sum f hb
    have : g = g' := Quiver.Hom.unop_inj (NPSUMap.ext_effects fun b hb' =>
      (hlub b hb').unique (hlub' b hb'))
    subst this
    exact ⟨hb, hg'⟩
  · rintro ⟨hb, hlim⟩
    obtain ⟨g', hg', hlub'⟩ := pvn_exists_sum f hb
    have : g = g' := Quiver.Hom.unop_inj (NPSUMap.ext' fun b =>
      Theses.A.VN.uwTendsto_unique (hlim b) (hg' b))
    subst this
    exact ⟨hb, hlub'⟩

/-- **SIG 15** (`ex:wstar`, main.tex:554, Example): a countable family in
`W*ᵒᵖ` is summable iff `∑_{j∈F} f_j(1) ≤ 1` for every finite `F ⊆ J`. -/
theorem pvn_summable_iff {J : Type} [Countable J] (f : J → (X ⟶ Y)) :
    Summable f ↔ ∀ F : Finset J, ∑ j ∈ F, ap (f j).unop 1 ≤ 1 := by
  constructor
  · intro h; exact ((pvn_sumsTo_iff f _).1 (sumsTo_sum h)).1
  · intro hb
    obtain ⟨g, hg, -⟩ := pvn_exists_sum f hb
    exact ((pvn_sumsTo_iff f g).2 ⟨hb, hg⟩).summable

theorem pvn_zero_eq (X Y : WStarPSU.{u}ᵒᵖ) :
    (0 : X ⟶ Y) = Quiver.Hom.op (show Y.unop ⟶ X.unop from NPSUMap.ofNCPSU (wZeroSU _ _)) := by
  have h := (pvn_sumsTo_iff (Empty.elim : Empty → (X ⟶ Y)) _).1 (sumsTo_of_isEmpty _)
  apply psuop_hom_ext
  intro b
  refine (Theses.A.VN.uwTendsto_unique (h.2 b) (uwTendsto_of_eventually_eq ?_)).trans
    (wZeroSU_apply (A := Y.unop.base.carrier) (B := X.unop.base.carrier) b).symm
  exact Filter.Eventually.of_forall fun F => by
    rw [Finset.eq_empty_of_isEmpty F, Finset.sum_empty]

theorem pvn_zero_apply (b : Y.unop.base) : ap (0 : X ⟶ Y).unop b = 0 := by
  rw [pvn_zero_eq]; rfl

theorem pvn_perp_iff (f g : X ⟶ Y) : Perp f g ↔ ap f.unop 1 + ap g.unop 1 ≤ 1 := by
  show SigmaPAM.Summable ![f, g] ↔ _
  rw [pvn_summable_iff]
  constructor
  · intro h
    have := h Finset.univ
    rwa [Fin.sum_univ_two] at this
  · intro h F
    refine le_trans ?_ h
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (f := fun j => ap (![f, g] j).unop 1) fun j _ _ => (ap _).one_nonneg
    simpa [Fin.sum_univ_two] using this

theorem pvn_ovee_apply {f g : X ⟶ Y} (h : Perp f g) (b : Y.unop.base) :
    ap (ovee f g h).unop b = ap f.unop b + ap g.unop b := by
  have hs := (pvn_sumsTo_iff ![f, g] _).1 (sumsTo_sum (show SigmaPAM.Summable ![f, g] from h))
  refine Theses.A.VN.uwTendsto_unique (hs.2 b) (uwTendsto_of_eventually_eq ?_)
  refine Filter.eventually_atTop.2 ⟨Finset.univ, fun F hF => ?_⟩
  rw [Finset.eq_univ_of_forall fun j => hF (Finset.mem_univ j), Fin.sum_univ_two]
  rfl

theorem pvn_one_of_retraction {X Y : WStarPSU.{u}ᵒᵖ} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) :
    ap i.unop 1 = 1 := by
  have h1 : ap i.unop (ap r.unop 1) = 1 := by
    rw [← psuop_comp_apply, h]; rfl
  refine le_antisymm (ap i.unop).subunital ?_
  calc (1 : X.unop.base) = ap i.unop (ap r.unop 1) := h1.symm
    _ ≤ ap i.unop 1 := (ap i.unop).mono (ap r.unop).subunital

end PSUHoms

/-! ### Countable coproducts of `W*ᵒᵖ` -/

section PSUCoproducts

variable {I : Type} {𝒜 : I → Type u} [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
  [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] [∀ i, Theses.VonNeumannAlgebra (𝒜 i)]
  {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Theses.VonNeumannAlgebra B]

omit [∀ i, Theses.VonNeumannAlgebra (𝒜 i)] [Theses.VonNeumannAlgebra B] in
theorem npsu_norm_le (f : NPSUMap B (𝒜 i)) (b : B) : ‖f b‖ ≤ ‖b‖ := by
  have h := Theses.A.CStar.russo_dye_cor f.toLinearMap (NPSUMap.isPositiveMap f.toPositiveLinearMap) b
  have h1 : ‖f.toLinearMap 1‖ ≤ 1 :=
    (CStarAlgebra.norm_le_norm_of_nonneg_of_le f.one_nonneg f.subunital).trans (by simp)
  calc ‖f b‖ ≤ ‖f.toLinearMap 1‖ * ‖b‖ := h
    _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖b‖ := one_mul _

/-- The tupling of npsu-maps into `⊕_i 𝒜_i`. -/
noncomputable def posTuple (f : ∀ i, NPSUMap B (𝒜 i)) : B →ₗ[ℂ] lp 𝒜 ∞ where
  toFun b := ⟨fun i => f i b, memℓp_infty_iff.2 ⟨‖b‖, by
    rintro _ ⟨i, rfl⟩; exact npsu_norm_le (f i) b⟩⟩
  map_add' a b := lp.ext (funext fun i => (f i).map_add a b)
  map_smul' c b := lp.ext (funext fun i => (f i).map_smul c b)

theorem posTuple_apply (f : ∀ i, NPSUMap B (𝒜 i)) (b : B) (i : I) :
    (posTuple f b : ∀ i, 𝒜 i) i = f i b := rfl

/-- **SIG 15** (`ex:wstar`, main.tex:548): `⊕_i 𝒜_i` is the product of the
`𝒜_i` in `W*` (npsu-maps): the tupling of npsu-maps is npsu, and unique.
The npsu-analogue of the tree's **47IV**.3. -/
theorem pos_products (f : ∀ i, NPSUMap B (𝒜 i)) :
    ∃! g : NPSUMap B (lp 𝒜 ∞), ∀ (i : I) (b : B), (g b : ∀ i, 𝒜 i) i = f i b := by
  have hmono : ∀ a b : B, a ≤ b → posTuple f a ≤ posTuple f b := fun a b h => by
    rw [Theses.A.VN.lp_infty_le_iff]
    intro i
    exact (f i).mono h
  have hnorm : Theses.PreservesDirSups ⇑(posTuple f) := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      rw [Theses.A.VN.lp_infty_le_iff]
      intro j
      exact ((f j).normal D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro u hu
      rw [Theses.A.VN.lp_infty_le_iff]
      intro j
      refine ((f j).normal D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      exact (Theses.A.VN.lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) j
  have hsu : posTuple f 1 ≤ 1 := by
    rw [Theses.A.VN.lp_infty_le_iff]
    intro i
    rw [lp.infty_coeFn_one]
    exact (f i).subunital
  refine ⟨⟨⟨posTuple f, hmono⟩, hnorm, hsu⟩, fun i b => rfl, fun g hg => ?_⟩
  refine NPSUMap.ext' fun b => lp.ext (funext fun i => ?_)
  exact hg i b

end PSUCoproducts

section PSUCoproducts2

variable {J : Type} (X : J → WStarPSU.{u}ᵒᵖ)

abbrev pvnFam (j : J) : Type u := (X j).unop.base.carrier

abbrev pvnIdx : Type := {j : J // Nontrivial (pvnFam X j)}

instance pvnFam_nontrivial (k : pvnIdx X) : Nontrivial (pvnFam X k.1) := k.2

abbrev pvnSumAlg : Type u := ↥(lp (fun k : pvnIdx X => pvnFam X k.1) ∞)

/-- The coproduct `∐_j 𝒜_j` of `W*ᵒᵖ`: the direct sum `⊕_j 𝒜_j`. -/
noncomputable abbrev pvnSum : WStarPSU.{u}ᵒᵖ := op (WStarPSU.of (WStar.of (pvnSumAlg X)))

def pvnCoord (a : pvnSumAlg X) (k : pvnIdx X) : pvnFam X k.1 := (a : ∀ k : pvnIdx X, pvnFam X k.1) k

open Classical in
noncomputable def pvnProj (j : J) : NPSUMap (pvnSumAlg X) (pvnFam X j) :=
  if h : Nontrivial (pvnFam X j) then
    NPSUMap.ofNCPSU ⟨Theses.A.Proc.nmiuNCP
      (Theses.B.Dils.lpProjNMIU (𝒜 := fun k : pvnIdx X => pvnFam X k.1) ⟨j, h⟩),
      le_of_eq (map_one (Theses.B.Dils.lpProjNMIU (𝒜 := fun k : pvnIdx X => pvnFam X k.1)
        ⟨j, h⟩).toStarAlgHom)⟩
  else NPSUMap.ofNCPSU (wZeroSU _ _)

theorem pvnProj_apply (j : J) (h : Nontrivial (pvnFam X j)) (a : pvnSumAlg X) :
    pvnProj X j a = pvnCoord X a ⟨j, h⟩ := by
  unfold pvnProj
  rw [dite_eq_left h]
  rfl

noncomputable def pvnProjOp (j : J) : X j ⟶ pvnSum X :=
  Quiver.Hom.op (show (pvnSum X).unop ⟶ (X j).unop from pvnProj X j)

noncomputable def pvnCofan : Cofan X := Cofan.mk (pvnSum X) (pvnProjOp X)

theorem pvnCofan_inj (j : J) : (pvnCofan X).inj j = pvnProjOp X j := rfl

theorem psubsingleton_of_not_nontrivial {j : J} (h : ¬ Nontrivial (pvnFam X j)) :
    Subsingleton (pvnFam X j) := not_nontrivial_iff_subsingleton.mp h

noncomputable def pvnDesc (t : Cofan X) : (pvnCofan X).pt ⟶ t.pt :=
  Quiver.Hom.op (show t.pt.unop ⟶ (pvnSum X).unop from
    (pos_products (𝒜 := fun k : pvnIdx X => pvnFam X k.1) (B := t.pt.unop.base.carrier)
      (fun k => ap (t.inj k.1).unop)).exists.choose)

theorem pvnDesc_apply (t : Cofan X) (k : pvnIdx X) (b : t.pt.unop.base) :
    pvnCoord X (ap (pvnDesc X t).unop b) k = ap (t.inj k.1).unop b :=
  (pos_products (𝒜 := fun k : pvnIdx X => pvnFam X k.1) (B := t.pt.unop.base.carrier)
      (fun k => ap (t.inj k.1).unop)).exists.choose_spec k b

/-- **SIG 15** (`ex:wstar`, main.tex:548): `⊕_j 𝒜_j` is the coproduct of
the `𝒜_j` in `W*ᵒᵖ`. -/
noncomputable def pvnCofanIsColimit : IsColimit (pvnCofan X) :=
  Cofan.IsColimit.mk _ (pvnDesc X)
    (fun t j => by
      apply psuop_hom_ext
      intro b
      erw [psuop_comp_apply]
      by_cases h : Nontrivial (pvnFam X j)
      · rw [pvnCofan_inj]
        exact (pvnProj_apply X j h _).trans (pvnDesc_apply X t ⟨j, h⟩ b)
      · have := psubsingleton_of_not_nontrivial X h
        exact Subsingleton.elim (α := pvnFam X j) _ _)
    (fun t m hm => by
      apply Quiver.Hom.unop_inj
      refine (pos_products (𝒜 := fun k : pvnIdx X => pvnFam X k.1) (B := t.pt.unop.base.carrier)
        (fun k => ap (t.inj k.1).unop)).unique (y₁ := m.unop) ?_ ?_
      · intro k b
        have := congrArg (fun φ => ap φ.unop b) (hm k.1)
        erw [psuop_comp_apply] at this
        exact (pvnProj_apply X k.1 k.2 _).symm.trans this
      · exact (pos_products (𝒜 := fun k : pvnIdx X => pvnFam X k.1)
          (B := t.pt.unop.base.carrier) (fun k => ap (t.inj k.1).unop)).exists.choose_spec)

end PSUCoproducts2

/-- **SIG 15** (`ex:wstar`, main.tex:548): `W*ᵒᵖ` has countable coproducts,
the ℓ^∞-direct sums. -/
instance pvnHasCountableCoproducts : HasCountableCoproducts WStarPSU.{u}ᵒᵖ :=
  ⟨fun J _ => ⟨fun F => by
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      HasColimit.mk ⟨_, pvnCofanIsColimit (F.obj ∘ Discrete.mk)⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor⟩⟩

/-! ### `W*ᵒᵖ` is a σ-effectus (SIG 15 as printed) -/

section PSUEffectus

open Theses.A.VN (UWTendsto)

theorem pvn_inl_one (B : WStarPSU.{u}ᵒᵖ) : ap (coprod.inl : B ⟶ B ⨿ B).unop 1 = 1 :=
  pvn_one_of_retraction _ (coprod.desc (𝟙 B) (𝟙 B)) (coprod.inl_desc _ _)

theorem pvn_inr_one (B : WStarPSU.{u}ᵒᵖ) : ap (coprod.inr : B ⟶ B ⨿ B).unop 1 = 1 :=
  pvn_one_of_retraction _ (coprod.desc (𝟙 B) (𝟙 B)) (coprod.inr_desc _ _)

section PProj

variable {J : Type} [Countable J] (X : J → WStarPSU.{u}ᵒᵖ)

noncomputable def pvnCoprodIso : ∐ X ≅ pvnSum X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (pvnCofanIsColimit X)

theorem ι_pvnCoprodIso (k : J) :
    Sigma.ι X k ≫ (pvnCoprodIso X).hom = (pvnCofan X).inj k :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk k)

theorem pvnKappa_le_one (j : J) (h : Nontrivial (pvnFam X j)) :
    Theses.A.Proc.lpKappa (𝒜 := fun k : pvnIdx X => pvnFam X k.1) ⟨j, h⟩ 1 ≤ 1 := by
  classical
  rw [Theses.A.VN.lp_infty_le_iff]
  intro k
  by_cases hk : k = ⟨j, h⟩
  · subst hk
    rw [Theses.A.Proc.lpKappa_apply_self, lp.infty_coeFn_one]; rfl
  · rw [Theses.A.Proc.lpKappa_apply_ne _ _ hk, lp.infty_coeFn_one]; exact zero_le_one

/-- The coprojection `κ_j : 𝒜_j → ⊕_k 𝒜_k` as an npsu-map. -/
noncomputable def pvnKappa (j : J) (h : Nontrivial (pvnFam X j)) :
    NPSUMap (pvnFam X j) (pvnSumAlg X) :=
  NPSUMap.ofNCPSU ⟨Theses.B.Dils.lpKappaNCP (𝒜 := fun k : pvnIdx X => pvnFam X k.1) ⟨j, h⟩,
    pvnKappa_le_one X j h⟩

theorem pvnKappa_apply (j : J) (h : Nontrivial (pvnFam X j)) (a : pvnFam X j) :
    pvnKappa X j h a = Theses.A.Proc.lpKappa (𝒜 := fun k : pvnIdx X => pvnFam X k.1) ⟨j, h⟩ a :=
  rfl

noncomputable def pvnKappaOp (j : J) (h : Nontrivial (pvnFam X j)) : pvnSum X ⟶ X j :=
  Quiver.Hom.op (show (X j).unop ⟶ (pvnSum X).unop from pvnKappa X j h)

theorem pvn_pproj_eq (j : J) (h : Nontrivial (pvnFam X j)) :
    pproj X j = (pvnCoprodIso X).hom ≫ pvnKappaOp X j h := by
  classical
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_pvnCoprodIso]
  by_cases hk : k = j
  · subst hk
    rw [ι_pproj_self]
    apply psuop_hom_ext
    intro a
    erw [psuop_comp_apply]
    show a = pvnProj X k (pvnKappa X k h a)
    symm
    rw [pvnProj_apply X k h, pvnKappa_apply]
    exact Theses.A.Proc.lpKappa_apply_self _ _
  · rw [ι_pproj_ne _ hk]
    apply psuop_hom_ext
    intro a
    erw [psuop_comp_apply]
    rw [pvn_zero_apply]
    show 0 = pvnProj X k (pvnKappa X j h a)
    symm
    by_cases hk' : Nontrivial (pvnFam X k)
    · rw [pvnProj_apply X k hk', pvnKappa_apply]
      exact Theses.A.Proc.lpKappa_apply_ne _ _ (fun e => hk (congrArg Subtype.val e))
    · have := psubsingleton_of_not_nontrivial X hk'
      exact Subsingleton.elim (α := pvnFam X k) _ _

end PProj

/-- **SIG 15** (`ex:wstar`, main.tex:548): `W*ᵒᵖ` is a σ-PAC. -/
instance pvnSigmaPAC : SigmaPAC WStarPSU.{u}ᵒᵖ where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · rw [pvn_sumsTo_iff] at hs ⊢
      refine ⟨fun F => ?_, fun b => ?_⟩
      · simp only [psuop_comp_apply]
        exact (Finset.sum_le_sum fun j _ => (ap (x j).unop).mono (ap g.unop).subunital).trans (hs.1 F)
      · simp only [psuop_comp_apply]
        exact hs.2 _
    · rw [pvn_sumsTo_iff] at hs ⊢
      have hsum : ∀ (F : Finset _) (b : Z.unop.base), ∑ j ∈ F, ap (f ≫ x j).unop b =
          ap f.unop (∑ j ∈ F, ap (x j).unop b) := fun F b => by
        simp only [psuop_comp_apply]
        exact ((ap f.unop).map_sum F _).symm
      refine ⟨fun F => ?_, fun b => ?_⟩
      · rw [hsum]
        exact ((ap f.unop).mono (hs.1 F)).trans (ap f.unop).subunital
      · have := (@Continuous.tendsto _ _ (Theses.A.VN.ultraweak _) (Theses.A.VN.ultraweak _) _
          (((Theses.A.VN.p_uwcont (ap f.unop).toPositiveLinearMap).out 2 0).mp (ap f.unop).normal)
          _).comp (hs.2 b)
        rw [psuop_comp_apply]
        exact this.congr fun F => (hsum F b).symm
  compatible_sum {J} _ {A B} f := by
    rintro ⟨g, hg⟩
    rw [pvn_summable_iff]
    intro F
    by_cases hB : Nontrivial B.unop.base.carrier
    · let X : J → WStarPSU.{u}ᵒᵖ := fun _ => B
      let H : NPSUMap (pvnSumAlg X) A.unop.base.carrier := ap (g ≫ (pvnCoprodIso X).hom).unop
      have hval : ∀ j, ap (f j).unop 1 = H (pvnKappa X j hB 1) := by
        intro j
        rw [← hg j, pvn_pproj_eq X j hB, ← Category.assoc]
        erw [psuop_comp_apply]
      have hsum : ∑ j ∈ F, ap (f j).unop 1 = H (∑ j ∈ F, pvnKappa X j hB 1) := by
        rw [Finset.sum_congr rfl fun j _ => hval j]
        exact (H.map_sum F _).symm
      rw [hsum]
      refine (H.mono ?_).trans H.subunital
      classical
      rw [Theses.A.VN.lp_infty_le_iff]
      rintro ⟨k, hk⟩
      rw [lp.infty_coeFn_one, Pi.one_apply, lp.coeFn_sum, Finset.sum_apply]
      simp only [pvnKappa_apply]
      by_cases hkF : k ∈ F
      · rw [Finset.sum_eq_single_of_mem k hkF fun j _ hjk =>
          Theses.A.Proc.lpKappa_apply_ne _ _ fun e => hjk (congrArg Subtype.val e).symm]
        rw [Theses.A.Proc.lpKappa_apply_self]
      · rw [Finset.sum_eq_zero fun j hj =>
          Theses.A.Proc.lpKappa_apply_ne _ _ fun e => hkF (by
            rw [show k = j from congrArg Subtype.val e]; exact hj)]
        exact zero_le_one
    · have := not_nontrivial_iff_subsingleton.mp hB
      have h0 : ∀ j, ap (f j).unop 1 = 0 := fun j => by
        rw [show (1 : B.unop.base.carrier) = 0 from Subsingleton.elim _ _]
        exact (ap (f j).unop).map_zero
      simp only [h0, Finset.sum_const_zero]
      exact zero_le_one
  untying {A B f g} h := by
    rw [pvn_summable_iff] at h ⊢
    have e : (fun j => ap (![f ≫ coprod.inl, g ≫ coprod.inr] j).unop 1) =
        fun j => ap (![f, g] j).unop 1 := by
      funext j
      fin_cases j
      · show ap (f ≫ coprod.inl).unop 1 = ap f.unop 1
        rw [psuop_comp_apply, pvn_inl_one]
      · show ap (g ≫ coprod.inr).unop 1 = ap g.unop 1
        rw [psuop_comp_apply, pvn_inr_one]
    intro F
    have := h F
    simp only [← e] at this ⊢
    exact this

variable {X Y : WStarPSU.{u}ᵒᵖ}

/-- The effect object `ℂ` of `W*ᵒᵖ`. -/
noncomputable abbrev psuI : WStarPSU.{u}ᵒᵖ := op (WStarPSU.of (WStar.of (ULift.{u} ℂ)))

/-- The truth predicate `1 : 𝔄 ⟶ ℂ`, the unit map `z ↦ z·1`. -/
noncomputable def psuOne (X : WStarPSU.{u}ᵒᵖ) : X ⟶ psuI :=
  Quiver.Hom.op (show psuI.unop ⟶ X.unop from NPSUMap.ofNCPSU (wUnitSU X.unop.base.carrier))

theorem psuOne_one (X : WStarPSU.{u}ᵒᵖ) : ap (psuOne X).unop 1 = 1 :=
  (wUnit X.unop.base.carrier).unital'

theorem pvn_comp_one_apply (f : X ⟶ Y) : ap (f ≫ psuOne Y).unop 1 = ap f.unop 1 := by
  rw [psuop_comp_apply, psuOne_one]

/-- The predicate `z ↦ z·a` of an effect `a`. -/
noncomputable def pvnPredOf (a : Theses.effects X.unop.base) : X ⟶ psuI :=
  Quiver.Hom.op (show psuI.unop ⟶ X.unop from NPSUMap.ofNCPSU (wEffect a.2.1 a.2.2))

theorem pvnPredOf_one (a : Theses.effects X.unop.base) : ap (pvnPredOf a).unop 1 = (a : X.unop.base) :=
  (wEffect_apply a.2.1 a.2.2 1).trans (by simp)

/-- The orthocomplement `p^⊥ = 1 - p` of a predicate. -/
noncomputable def pvnOrth (p : X ⟶ psuI) : X ⟶ psuI :=
  pvnPredOf ⟨1 - ap p.unop 1, sub_nonneg.mpr (ap p.unop).subunital,
    sub_le_self 1 (ap p.unop).one_nonneg⟩

theorem pvnOrth_one (p : X ⟶ psuI) : ap (pvnOrth p).unop 1 = 1 - ap p.unop 1 :=
  pvnPredOf_one _

/-- **SIG 15** (`ex:wstar`, main.tex:548, Example), as printed: the opposite
of the category `W*` of W*-algebras (von Neumann algebras) and subunital
normal positive maps is a σ-effectus with `ℂ` as unit; summability and sums
as in `pvn_summable_iff` and `pvn_sumsTo_iff`. -/
noncomputable instance pvnSigmaEffectus : SigmaEffectus WStarPSU.{u}ᵒᵖ :=
  { pvnSigmaPAC with
    I := psuI
    one := psuOne
    orth := pvnOrth
    perp_orth := fun {X} p => by
      rw [pvn_perp_iff, pvnOrth_one]
      exact le_of_eq (add_sub_cancel _ _)
    ovee_orth := fun {X} p => by
      refine Quiver.Hom.unop_inj (NPSUMap.scal_ext ?_)
      have hperp : Perp p (pvnOrth p) := (pvn_perp_iff p (pvnOrth p)).2
        (by rw [pvnOrth_one]; exact le_of_eq (add_sub_cancel _ _))
      have h := pvn_ovee_apply hperp 1
      rw [pvnOrth_one, add_sub_cancel] at h
      exact h.trans (psuOne_one X).symm
    orth_unique := fun {X p q} h heq => by
      refine Quiver.Hom.unop_inj (NPSUMap.scal_ext ?_)
      have h1 := pvn_ovee_apply h 1
      rw [heq, psuOne_one] at h1
      show ap q.unop 1 = ap (pvnOrth p).unop 1
      rw [pvnOrth_one, h1]
      abel
    eq_zero_of_perp_one := fun {X p} h => by
      rw [pvn_perp_iff, psuOne_one] at h
      have h4 : ap p.unop 1 = 0 :=
        le_antisymm (by simpa using sub_le_sub_right h (1 : X.unop.base.carrier))
          (ap p.unop).one_nonneg
      refine Quiver.Hom.unop_inj (NPSUMap.scal_ext ?_)
      exact h4.trans (pvn_zero_apply (X := X) (Y := psuI) 1).symm
    eq_zero_of_one_zero := fun {X Y f} h => by
      have h2 : ap f.unop 1 = 0 := by
        rw [← pvn_comp_one_apply, h, pvn_zero_apply]
      refine Quiver.Hom.unop_inj (NPSUMap.ext' fun y => ?_)
      rw [NPSUMap.eq_zero_of_one _ h2 y]
      exact (pvn_zero_apply y).symm
    perp_of_one_perp := fun {X Y f g} h => by
      rw [pvn_perp_iff, pvn_comp_one_apply, pvn_comp_one_apply] at h
      exact (pvn_perp_iff f g).2 h }

/-- The effect `p(1)` of a predicate `p : 𝔄 ⟶ ℂ` of `W*ᵒᵖ`. -/
noncomputable def pvnPredVal (p : X ⟶ psuI) : Theses.effects X.unop.base :=
  ⟨ap p.unop 1, (ap p.unop).one_nonneg, (ap p.unop).subunital⟩

/-- **SIG 15** (`ex:wstar`, main.tex:566): in `W*ᵒᵖ` the predicates are the effects:
`Pred(𝔄) ≅ [0,1]_𝔄` via `p ↦ p(1)`, with `p ⊥ q ⟺ p(1) + q(1) ≤ 1`,
`(p ⊕ q)(1) = p(1) + q(1)`, `1 ↦ 1`, `p^⊥ ↦ 1 - p(1)`. -/
theorem pvn_pred_effects (X : WStarPSU.{u}ᵒᵖ) :
    (∃ e : Pred X ≃ Theses.effects X.unop.base, ∀ p, (e p : X.unop.base) = ap p.unop 1) ∧
      (∀ p q : Pred X, Perp p q ↔ ap p.unop 1 + ap q.unop 1 ≤ 1) ∧
      (∀ (p q : Pred X) (h : Perp p q), ap (ovee p q h).unop 1 = ap p.unop 1 + ap q.unop 1) ∧
      ap (truth X : Pred X).unop 1 = 1 ∧
      ∀ p : Pred X, ap (orth p : Pred X).unop 1 = 1 - ap p.unop 1 := by
  refine ⟨⟨{ toFun := pvnPredVal
             invFun := pvnPredOf
             left_inv := fun p => Quiver.Hom.unop_inj (NPSUMap.scal_ext (pvnPredOf_one _))
             right_inv := fun a => Subtype.ext (pvnPredOf_one a) }, fun p => rfl⟩,
    fun p q => pvn_perp_iff p q, fun p q h => pvn_ovee_apply h 1, psuOne_one X,
    fun p => pvnOrth_one p⟩

/-- **SIG 15** (`ex:wstar`, main.tex:568): the total maps of `W*ᵒᵖ` are precisely the
unital maps. -/
theorem pvn_isTotal_iff (f : X ⟶ Y) : IsTotal f ↔ ap f.unop 1 = 1 := by
  show f ≫ psuOne Y = psuOne X ↔ _
  constructor
  · intro h
    have := pvn_comp_one_apply f
    rw [h, psuOne_one] at this
    exact this.symm
  · intro h
    refine Quiver.Hom.unop_inj (NPSUMap.scal_ext ?_)
    exact (pvn_comp_one_apply f).trans (h.trans (psuOne_one X).symm)

/-- **SIG 15** (`ex:wstar`, main.tex:561): the states on `𝔄` in `W*ᵒᵖ` are the unital
normal positive maps `𝔄 → ℂ`, the normal states. -/
theorem pvn_stat_iff (ω : psuI ⟶ X) : IsTotal ω ↔ ap ω.unop 1 = 1 := pvn_isTotal_iff ω

end PSUEffectus

/-- **SIG 15**: the inclusion `W*_cpsu → W*` (every ncpsu-map is npsu). -/
noncomputable def cpsuToPsu : WStarCPSU.{u} ⥤ WStarPSU.{u} where
  obj X := WStarPSU.of X.base
  map f := NPSUMap.ofNCPSU f
  map_id _ := NPSUMap.ext' fun a => su_id_apply a
  map_comp f g := NPSUMap.ext' fun a => su_comp_apply f g a

end Papers.SIG
