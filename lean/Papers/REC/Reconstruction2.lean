/-
Papers/REC/Reconstruction2.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): §5 "The reconstruction", second half —
REC 121 (V_A is a JB-algebra) and the main theorems REC 102, 103 (with Remark 104).

`Papers/REC/Reconstruction.lean` holds §5 up to REC 120; this file continues it.  The
split lets REC 121 use the proved 9.43 part (`jb_of_chainDense`,
`Papers/REC/JordanFromChains.lean`, with the Jordan symmetry `jordan_symmetry` of
`Papers/REC/JordanSymmetry.lean`) and the chain density of `V_A` (`va_chainDense`,
`Papers/REC/SpectralChains.lean`), which both build on the first half.  So REC 121,
and REC 102/103 after it, no longer take the named hypothesis
`AlfsenShultzJordanFromDerivations`: their remaining named hypotheses are
`AlfsenShultzResolventCriterion` (REC 120) and `WeteringStateOrderLemma C` (REC 119).
-/
import Papers.REC.JordanFromChains
import Papers.REC.SpectralChains

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Idempotents
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff
open scoped unitInterval NNReal

namespace Papers.REC

universe u v w

/-! ### REC 121 -/

section Rec121

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus
open scoped Papers.SEA

variable (σs : ScalarSplit C)

theorem list_attach_map_sum {α : Type*} {M : Type*} [AddCommMonoid M] {P : α → Prop}
    (l : List α) (hl : ∀ x ∈ l, P x) (F : α → M) :
    ((l.attach.map fun x => (⟨x.1, hl x.1 x.2⟩ : {a // P a})).map fun y => F y.1).sum =
      (l.map F).sum := by
  rw [List.map_map]
  simp

/-- **REC 121** (`prop:is-JB-algebra`, short.tex:2226, Proposition): `V_A` is a
JB-algebra, with `p * a = ½ (a + D_p a)` for sharp `p`.  The paper's proof invokes
Alfsen–Shultz, *Geometry*, Thm. 9.48 (via 9.43) outside its hypotheses; here the
copied argument is *proved* (`jb_of_chainDense`, with the Jordan symmetry
`jordan_symmetry`), and no A–S 9.4x hypothesis is taken.  Its inputs are supplied here:
`V_A` is a Banach order unit space (REC 41), the sharp predicates with the maps `asrt_p`
are compressions (idempotent, `asrt_p 1 = p`, `asrt_p asrt_{p⊥} = 0`, and
`asrt_p w = 0 ⟺ asrt_{p⊥} w = w` for `w ≥ 0`), every `D_p` is an order derivation
(REC 120), and chain combinations of pairwise commuting sharp predicates are norm dense
(REC 58 in chain form, `va_chainDense`). -/
theorem rec121 (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C) (A : C) :
    ∃ _ : Mul (VA σs A), JBAlgebra (VA σs A) ∧
      ∀ q : CPt σs A, IsSharp q.1 → ∀ w, GP.gmap q * w = (2⁻¹ : ℝ) • (w + Dop σs q w) := by
  let ι := {q : CPt σs A // Papers.SEA.IsIdempotent q}
  let e : ι → VA σs A := fun i => GP.gmap i.1
  let U : ι → VA σs A →ₗ[ℝ] VA σs A := fun i => Uop σs i.1
  let c : ι → ι := fun i => ⟨orth i.1, i.2.compl⟩
  have hsh : ∀ i : ι, IsSharp i.1.1 := fun i =>
    isSharp_of_isIdempotent ((cpt_idem_iff σs i.1).1 i.2)
  obtain ⟨m, hjb, hform⟩ := jb_of_chainDense (VA_isOUS σs A) (VA_banach σs A) ι e U c
    (fun i j h => Subtype.ext (GP.gmap_injective h))
    (fun i => ⟨GP.gmap_nonneg _, GP.gmap_le_gunit _⟩)
    (fun i => by
      show GP.gmap (orth i.1) = ouUnit (VA σs A) - GP.gmap i.1
      rw [← gmap_add_orth' σs i.1]; abel)
    (fun i => ⟨fun w hw => Uop_nonneg σs i.1 hw, Uop_unit σs i.1,
      gp_linearMap_ext fun b => by
        show Uop σs i.1 (Uop σs i.1 (GP.gmap b)) = Uop σs i.1 (GP.gmap b)
        rw [Uop_gmap, Uop_gmap, (Papers.SEA.commutes_refl i.1).assoc, i.2],
      gp_linearMap_ext fun b => by
        show Uop σs i.1 (Uop σs (orth i.1) (GP.gmap b)) = 0
        rw [Uop_gmap, Uop_gmap, (Papers.SEA.commutes_orth_self i.1).assoc, i.2.seq_orth,
          Papers.SEA.zero_seq, GP.gmap_zero]⟩)
    (fun i w hw => by
      obtain ⟨p₀, rfl⟩ := GP.Vec.exists_of_zero_le hw
      obtain ⟨r, b, rfl⟩ := GP.Cone.exists_mk p₀
      rw [← gp_rsmul_gmap]
      show Uop σs i.1 ((r : ℝ) • GP.gmap b) = 0 ↔
        Uop σs (orth i.1) ((r : ℝ) • GP.gmap b) = (r : ℝ) • GP.gmap b
      rw [map_smul, map_smul, Uop_gmap, Uop_gmap]
      rcases eq_or_ne (r : ℝ) 0 with hr | hr
      · simp [hr]
      rw [smul_eq_zero, or_iff_right hr, ← GP.gmap_zero]
      constructor
      · intro h
        have h1 : i.1 ⊙ b = 0 := GP.gmap_injective h
        have h2 : b ≼ orth i.1 := by
          have := ((Papers.SEA.sea17_5 i.2.compl b).2.2.2).2
          rw [Papers.SEA.orth_orth] at this; exact this h1
        rw [((Papers.SEA.sea17_5 i.2.compl b).1).1 h2]
      · intro h
        have h1 : orth i.1 ⊙ b = b :=
          GP.gmap_injective ((smul_right_injective _ hr) h)
        have h2 : b ≼ orth i.1 := ((Papers.SEA.sea17_5 i.2.compl b).1).2 h1
        have := ((Papers.SEA.sea17_5 i.2.compl b).2.2.2).1 h2
        rw [Papers.SEA.orth_orth] at this
        rw [this])
    (fun i => rec120 σs hRC h119 i.1 (hsh i))
    (va_chainDense σs A)
  refine ⟨m, hjb, fun q hq w => ?_⟩
  have := hform ⟨q, (cpt_idem_iff σs q).2 (isIdempotent_of_isSharp hq)⟩ w
  simpa [Dop, e, U, c] using this

end Rec121


/-! ## §5.5 The main theorems -/

/-! ### The categories `CBA`, `JB_npc`, `JBW_npc` -/

section Cats

/-- **REC 102**: `CBA`, the category of complete Boolean algebras and monotone maps
(as printed). -/
structure CBACat : Type (u + 1) where
  carrier : Type u
  [ba : BooleanAlgebra carrier]
  complete : ∀ S : Set carrier, ∃ j, IsLUB S j

attribute [instance] CBACat.ba

instance : Category CBACat.{u} where
  Hom A B := { f : A.carrier → B.carrier // Monotone f }
  id _ := ⟨id, monotone_id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A linear map between order unit spaces is a **normal positive contraction**
(REC 47, 48): positive, `‖f v‖ ≤ ‖v‖`, and normal. -/
def IsNPC {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
    (f : V →ₗ[ℝ] W) : Prop :=
  (∀ v, 0 ≤ v → 0 ≤ f v) ∧ (∀ v, ousNorm W (f v) ≤ ousNorm V v) ∧ IsNormalMap f

section NPC

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
  {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]
  {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [PartialOrder Z] [OrderUnitSpace Z]

theorem monotone_of_pos {f : V →ₗ[ℝ] W} (h : ∀ v, 0 ≤ v → 0 ≤ f v) : Monotone f :=
  fun v w hvw => by have := h _ (sub_nonneg.2 hvw); rwa [map_sub, sub_nonneg] at this

theorem isNPC_id : IsNPC (LinearMap.id : V →ₗ[ℝ] V) :=
  ⟨fun _ h => h, fun _ => le_rfl, fun S s _ _ hs => by simpa using hs⟩

theorem isNPC_comp {f : V →ₗ[ℝ] W} {g : W →ₗ[ℝ] Z} (hf : IsNPC f) (hg : IsNPC g) :
    IsNPC (g ∘ₗ f) := by
  refine ⟨fun v hv => hg.1 _ (hf.1 _ hv), fun v => (hg.2.1 _).trans (hf.2.1 _),
    fun S s hne hdir hs => ?_⟩
  have h1 := hf.2.2 S s hne hdir hs
  have hmono := monotone_of_pos hf.1
  have h2 := hg.2.2 (f '' S) (f s) (hne.image _) (hdir.mono_comp hmono) h1
  rw [Set.image_image] at h2; exact h2

/-- A positive map with `0 ≤ f 1 ≤ 1` is a contraction. -/
theorem contraction_of_pos {f : V →ₗ[ℝ] W} (hpos : ∀ v, 0 ≤ v → 0 ≤ f v)
    (h1 : f (ouUnit V) ≤ ouUnit W) (v : V) : ousNorm W (f v) ≤ ousNorm V v := by
  by_cases hu : ouUnit V = 0
  · rw [ou_eq_zero_of_unit_eq_zero hu v, map_zero]
    exact le_trans (ousNorm_le_rc le_rfl (by simp) (by simp)) (ousNorm_nonneg_rc _)
  refine le_csInf (ousNormSet_nonempty v) fun l hl => ?_
  have hl0 := ousNormSet_nonneg hu hl
  have hf1 : 0 ≤ f (ouUnit V) := hpos _ ou_unit_nonneg
  have a1 := hpos _ (sub_nonneg.2 hl.1)
  rw [map_sub, map_neg, map_smul, sub_neg_eq_add] at a1
  have a2 := hpos _ (sub_nonneg.2 hl.2)
  rw [map_sub, map_smul] at a2
  refine ousNorm_le_rc hl0 ?_ ?_
  · calc -(l • ouUnit W) ≤ -(l • f (ouUnit V)) := neg_le_neg (ou_smul_le_smul hl0 h1)
      _ ≤ f v := neg_le_iff_add_nonneg.2 a1
  · calc f v ≤ l • f (ouUnit V) := sub_nonneg.1 a2
      _ ≤ l • ouUnit W := ou_smul_le_smul hl0 h1

end NPC

/-- **REC 102**: `JB_npc`, JB-algebras (REC 44) with normal positive linear
contractions (the paper does not define it; "analogously to `JBW_npc`", REC 48). -/
structure JBnpcCat : Type (u + 1) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [po : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [mul : Mul carrier]
  jb : JBAlgebra carrier

attribute [instance] JBnpcCat.acg JBnpcCat.mod JBnpcCat.po JBnpcCat.ous JBnpcCat.mul

instance : Category JBnpcCat.{u} where
  Hom A B := { f : A.carrier →ₗ[ℝ] B.carrier // IsNPC f }
  id _ := ⟨LinearMap.id, isNPC_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, isNPC_comp f.2 g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **REC 48** (`def:JBW-algebra`, short.tex:901, Definition), the category part:
`JBW_npc`, JBW-algebras with normal positive linear contractions. -/
structure JBWnpcCat : Type (u + 1) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [po : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [mul : Mul carrier]
  jbw : JBWAlgebra carrier

attribute [instance] JBWnpcCat.acg JBWnpcCat.mod JBWnpcCat.po JBWnpcCat.ous JBWnpcCat.mul

instance : Category JBWnpcCat.{u} where
  Hom A B := { f : A.carrier →ₗ[ℝ] B.carrier // IsNPC f }
  id _ := ⟨LinearMap.id, isNPC_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, isNPC_comp f.2 g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end Cats

/-! ### `Pred(f)` on `V_A` is a normal positive contraction -/

section PredLin

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

variable (σs : ScalarSplit C)

/-- In a directed-complete Gudder–Pulmannová space, a supremum relative to `[0,1]`
of a non-empty directed subset of `[0,1]` is its supremum. -/
theorem gp_isLUB_of_rel {E : Type u} [EffectAlgebra E] [EffectModule I E]
    [Papers.OAP.DirectedComplete E] {D : Set (GP.Vec E)}
    (hD : D ⊆ Set.Icc 0 (ouUnit (GP.Vec E))) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    {t : GP.Vec E} (ht : Papers.OAP.IsLUBIn (Set.Icc 0 (ouUnit (GP.Vec E))) D t) :
    IsLUB D t := by
  obtain ⟨t', ht'⟩ := (Papers.OAP.oap60_directed.1 Papers.OAP.gp_directedComplete) D hne hdir
    ⟨ouUnit _, fun d hd => (hD hd).2⟩
  obtain ⟨d, hd⟩ := hne
  have ht'I : t' ∈ Set.Icc 0 (ouUnit (GP.Vec E)) :=
    ⟨(hD hd).1.trans (ht'.1 hd), ht'.2 fun d hd => (hD hd).2⟩
  have e : t = t' := le_antisymm (ht.2.2 t' ht'I ht'.1) (ht'.2 ht.2.1)
  rw [e]; exact ht'

theorem stateLin_unit_le {B A : C} (g : B ⟶ A) :
    stateLin σs g (ouUnit (VA σs A)) ≤ ouUnit (VA σs B) := by
  show stateLin σs g (GP.gmap 1) ≤ GP.gmap 1
  rw [stateLin_gmap]
  refine gmap_mono ((PredPart.le_iff _).2 ?_)
  show g ≫ (truth A ≫ orth σs.s) ≼ truth B ≫ orth σs.s
  rw [← Category.assoc]
  exact le_comp_right' (pred_le_truth _) _

open scoped Papers.OAP in
/-- `Pred(g)` on `V_A` preserves suprema of directed sets (normality of the
effectus, REC 30, transported to `V_A`). -/
theorem stateLin_normal {B A : C} (g : B ⟶ A) : IsNormalMap (stateLin σs g) := by
  intro S s hne hdir hs
  set T := stateLin σs g with hT
  have hTmono : Monotone T := monotone_of_pos fun v hv => stateLin_nonneg σs g hv
  refine ⟨?_, fun w hw => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hTmono (hs.1 hx)
  obtain ⟨s₀, hs₀⟩ := hne
  set S' : Set (VA σs A) := {x | x ∈ S ∧ s₀ ≤ x} with hS'
  have hcof : ∀ x ∈ S, ∃ z ∈ S', x ≤ z := fun x hx => by
    obtain ⟨z, hz, hxz, h0z⟩ := hdir x hx s₀ hs₀; exact ⟨z, ⟨hz, h0z⟩, hxz⟩
  have hdir' : DirectedOn (· ≤ ·) S' := by
    rintro x ⟨hx, hx0⟩ y ⟨hy, -⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z, ⟨hz, hx0.trans hxz⟩, hxz, hyz⟩
  have hsS' : IsLUB S' s := ⟨fun x hx => hs.1 hx.1, fun u hu => hs.2 fun x hx => by
    obtain ⟨z, hz, hxz⟩ := hcof x hx; exact hxz.trans (hu hz)⟩
  -- move `S'` into `[0,1]`
  obtain ⟨n₁, h11, -⟩ := Papers.OAP.oap58_orderUnit s₀
  obtain ⟨n₂, -, h22⟩ := Papers.OAP.oap58_orderUnit s
  set N : ℝ := n₁ + n₂ + 1 with hN
  have hN0 : 0 < N := by positivity
  have hsym : ∀ x, s₀ ≤ x → x ≤ s → x ∈ Papers.OAP.symIcc (VA σs A) N := fun x h1 h2 =>
    ⟨(neg_le_neg (ou_smul_unit_mono (by rw [hN]; linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]))).trans
      (h11.trans h1),
      h2.trans (h22.trans (ou_smul_unit_mono (by rw [hN]; linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)])))⟩
  set G := Papers.OAP.affIso (V := VA σs A) N hN0 with hGdef
  have hGmem : ∀ x ∈ Papers.OAP.symIcc (VA σs A) N, G x ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    fun x hx => by
      rw [← Set.mem_preimage, Papers.OAP.affIso_preimage]; exact hx
  have hGS'I : ∀ x ∈ S', G x ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    fun x hx => hGmem x (hsym x hx.2 (hs.1 hx.1))
  have hsI : G s ∈ Set.Icc 0 (ouUnit (VA σs A)) :=
    hGmem s (hsym s (hs.1 hs₀) le_rfl)
  have hGS : IsLUB (G '' S') (G s) := ⟨by rintro _ ⟨x, hx, rfl⟩; exact G.monotone (hsS'.1 hx),
    fun u hu => by
      have : s ≤ G.symm u := hsS'.2 fun x hx => G.le_symm_apply.2 (hu ⟨x, hx, rfl⟩)
      exact G.le_symm_apply.1 this⟩
  -- the corresponding set of effects
  set D : Set (CPt σs A) := {a | GP.gmap a ∈ G '' S'} with hD
  have hDimg : GP.gmap '' D = G '' S' := by
    ext y; constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := GP.gmap_surjective_Icc (hGS'I x hx)
      exact ⟨a, by rw [hD, Set.mem_ofPred_eq, ha]; exact ⟨x, hx, rfl⟩, ha⟩
  obtain ⟨as, has⟩ := GP.gmap_surjective_Icc hsI
  have hDsup : IsLUB D as := Papers.OAP.gmap_isLUBIn_iff.2 (by
    rw [hDimg, has]; exact ⟨hsI, hGS.1, fun w _ hw => hGS.2 hw⟩)
  have hDdir : IsUpDirected D := by
    rintro a ⟨x, hx, hax⟩ b ⟨y, hy, hby⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir' x hx y hy
    obtain ⟨c, hc⟩ := GP.gmap_surjective_Icc (hGS'I z hz)
    refine ⟨c, ⟨z, hz, hc.symm⟩, ?_, ?_⟩
    · exact Papers.OAP.gmap_le_gmap_iff.1 (by rw [← hax, hc]; exact G.monotone hxz)
    · exact Papers.OAP.gmap_le_gmap_iff.1 (by rw [← hby, hc]; exact G.monotone hyz)
  have hDsup' : IsSupOf D as := ⟨fun x hx => hDsup.1 hx, fun u hu => hDsup.2 hu⟩
  -- in `Pred(A)`, then through `g` by normality
  have hv := cpt_isSup_val σs hDdir hDsup'
  have hDdir' : IsUpDirected (Subtype.val '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hDdir x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩, (PredPart.le_iff _).1 hxz, (PredPart.le_iff _).1 hyz⟩
  have hn := (normal (C := C)).2 g _ _ hDdir' hv
  set F : CPt σs A → CPt σs B := fun a => cptMk σs (A := B) (g ≫ a.1)
    (by rw [Category.assoc, a.2]) with hF
  have hFsup : IsLUB (F '' D) (F as) := by
    refine ⟨?_, fun u hu => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (PredPart.le_iff _).2 (hn.1 _ ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
    · refine (PredPart.le_iff _).2 (hn.2 _ ?_)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact (PredPart.le_iff _).1 (hu ⟨x, hx, rfl⟩)
  have hrel := Papers.OAP.gmap_isLUBIn_iff.1 hFsup
  have himg : GP.gmap '' (F '' D) = T '' (G '' S') := by
    rw [← hDimg, Set.image_image, Set.image_image]
    ext y; simp only [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by rw [hT, stateLin_gmap]⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by rw [hT, stateLin_gmap]⟩
  have hFs : GP.gmap (F as) = T (G s) := by rw [← has, hT, stateLin_gmap]
  rw [himg, hFs] at hrel
  have hsub : T '' (G '' S') ⊆ Set.Icc 0 (ouUnit (VA σs B)) := by
    rw [← himg]; rintro _ ⟨a, -, rfl⟩; exact ⟨GP.gmap_nonneg _, GP.gmap_le_gunit _⟩
  have hLUB := gp_isLUB_of_rel hsub
    ((Set.Nonempty.image G (⟨s₀, ⟨hs₀, le_rfl⟩⟩ : S'.Nonempty)).image T)
    ((hdir'.mono_comp G.monotone).mono_comp hTmono) hrel
  -- undo the affine map
  have hTG : ∀ x, T (G x) = (2 * N)⁻¹ • (T x + N • T (ouUnit (VA σs A))) := fun x => by
    rw [hGdef, Papers.OAP.affIso_apply, map_smul, map_add, map_smul]
  have hw' : ∀ x ∈ S', T (G x) ≤ (2 * N)⁻¹ • (w + N • T (ouUnit (VA σs A))) := fun x hx => by
    rw [hTG]
    exact smul_le_smul_of_nonneg_left (add_le_add_left (hw ⟨x, hx.1, rfl⟩) _) (by positivity)
  have h1 := hLUB.2 (by rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact hw' x hx)
  rw [hTG] at h1
  have h2 := le_of_smul_le_smul_left h1 (by positivity : (0 : ℝ) < (2 * N)⁻¹)
  exact (add_le_add_iff_right _).1 h2

/-- `Pred(g)` on `V_A` is a normal positive contraction (a morphism of `JB_npc`,
`JBW_npc`). -/
theorem stateLin_isNPC {B A : C} (g : B ⟶ A) : IsNPC (stateLin σs g) :=
  ⟨fun _ hv => stateLin_nonneg σs g hv,
    contraction_of_pos (fun _ hv => stateLin_nonneg σs g hv) (stateLin_unit_le σs g),
    stateLin_normal σs g⟩

theorem stateLin_comp {B B' A : C} (f : B' ⟶ B) (g : B ⟶ A) :
    stateLin σs (f ≫ g) = stateLin σs f ∘ₗ stateLin σs g :=
  gp_linearMap_ext fun a => by
    rw [LinearMap.comp_apply, stateLin_gmap, stateLin_gmap, stateLin_gmap]
    congr 1; exact Subtype.ext (Category.assoc _ _ _)

end PredLin


/-! ### Complete Boolean algebra structures on predicate spaces -/

section CBAOnSec

/-- A complete Boolean algebra structure on an effect algebra, whose lattice order
is the effect-algebra order `≼`. -/
structure CBAOn (E : Type u) [EffectAlgebra E] where
  ba : BooleanAlgebra E
  le_iff : ∀ a b : E, a ≼ b ↔ (letI := ba; a ≤ b)
  complete : ∀ S : Set E, ∃ j, (letI := ba; IsLUB S j)

/-- Transport along an isomorphism of effect algebras. -/
noncomputable def CBAOn.ofEAIso {E F : Type u} [EffectAlgebra E] [EffectAlgebra F]
    (φ : EAIso E F) (hF : CBAOn F) : CBAOn E :=
  let e : E ≃ F := ⟨φ.hom.toFun, φ.inv.toFun, φ.inv_hom, φ.hom_inv⟩
  let _ : BooleanAlgebra F := hF.ba
  { ba := e.booleanAlgebra
    le_iff := fun a b => (φ.le_iff).trans (hF.le_iff _ _)
    complete := fun S => by
      let _ := e.booleanAlgebra
      obtain ⟨j, hj⟩ := hF.complete (e '' S)
      refine ⟨e.symm j, fun x hx => ?_, fun u hu => ?_⟩
      · show e x ≤ e (e.symm j)
        rw [e.apply_symm_apply]; exact hj.1 ⟨x, hx, rfl⟩
      · show e (e.symm j) ≤ e u
        rw [e.apply_symm_apply]
        exact hj.2 (by rintro _ ⟨x, hx, rfl⟩; exact hu hx) }

variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
  [∀ X Y : D, PCM (X ⟶ Y)] [FinPAC D] [EffectusPartialForm D]

/-- The predicate functor `Pred : D → CBAᵒᵖ`, `A ↦ Pred(A)` (with a complete Boolean
algebra structure on each `Pred(A)` whose order is `≼`), `f ↦ (q ↦ q ∘ f)`. -/
noncomputable def cbaPredFunctor (hB : ∀ P : D, CBAOn (Pred P)) : D ⥤ CBACat.{v}ᵒᵖ where
  obj P := Opposite.op (@CBACat.mk (Pred P) (hB P).ba (hB P).complete)
  map {P Q} f := Quiver.Hom.op ⟨fun q => f ≫ q, fun a b h =>
    ((hB P).le_iff _ _).1 (comp_le_comp f (((hB Q).le_iff _ _).2 h))⟩
  map_id P := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; funext q; exact Category.id_comp q
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; funext q; exact Category.assoc _ _ q

theorem cbaPredFunctor_map_eq (hB : ∀ P : D, CBAOn (Pred P)) {P Q : D} (f g : P ⟶ Q) :
    (cbaPredFunctor hB).map f = (cbaPredFunctor hB).map g ↔ ∀ q : Pred Q, f ≫ q = g ≫ q := by
  constructor
  · intro h q
    have h1 := congrArg Quiver.Hom.unop h
    have h2 := congrArg Subtype.val h1
    exact congrFun h2 q
  · intro h
    apply Quiver.Hom.unop_inj; apply Subtype.ext; funext q; exact h q

/-- `Pred : D → CBAᵒᵖ` is faithful iff `D` is separated by predicates. -/
theorem cbaPredFunctor_faithful_iff (hB : ∀ P : D, CBAOn (Pred P)) :
    (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates D := by
  constructor
  · intro hF P Q f g h
    exact (cbaPredFunctor hB).map_injective ((cbaPredFunctor_map_eq hB f g).2 h)
  · intro hs
    exact ⟨fun {P Q} {f g} h => hs f g ((cbaPredFunctor_map_eq hB f g).1 h)⟩

end CBAOnSec

/-! ### REC 102 -/

section Rec102

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

variable (σs : ScalarSplit C)

/-- The Boolean part `s · Pred(A)` is a complete Boolean algebra (REC 96, 97, for a
given splitting). -/
theorem part_cba (A : C) : Nonempty (CBAOn (PredPart σs.hs A)) := by
  have hOA := σs.isOrthoalgebra separatedByStates A
  have hid := part_idem σs.hs hOA
  have hu : SEA.IsIdempotent (truth A ≫ σs.s) := hid 1
  let _ : SEA (PredPart σs.hs A) := partSEA σs.hs hu
  obtain ⟨B, hB⟩ := rec96 hOA
  exact ⟨⟨B, fun a b => (hB a b).1, boolean_complete_of_dc B (fun a b => (hB a b).1)
    (PredPart.directedComplete _ ((normal (C := C)).1 A))⟩⟩

/-- The complete Boolean algebra structure on the predicates of an object of the
Boolean part `C₁` of REC 102 (transported along `partPredIso`). -/
noncomputable def cbaOnPart (P : (dcSplitting σs separatedByStates).ε.Part) :
    CBAOn (Pred P) :=
  CBAOn.ofEAIso (partPredIso σs.hs (isSharp_of_states σs.hs separatedByStates)
    (Or.inl separatedByStates) P) (part_cba σs P.obj.X).some

/-- The predicate functor `C₁ → CBAᵒᵖ` of REC 102. -/
noncomputable abbrev rec102_cbaFunctor :
    (dcSplitting σs separatedByStates).ε.Part ⥤ CBACat.{v}ᵒᵖ :=
  cbaPredFunctor (cbaOnPart σs)

variable (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- The Jordan product on `V_A` given by REC 121. -/
noncomputable def jbMul (A : C) : Mul (VA σs A) := (rec121 σs hRC h119 A).choose

theorem jbMul_spec (A : C) : @JBAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) :=
  (rec121 σs hRC h119 A).choose_spec.1

/-- `V_A` as an object of `JB_npc`. -/
noncomputable def jbObj (A : C) : JBnpcCat.{v} :=
  @JBnpcCat.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (jbMul_spec σs hRC h119 A)

/-- `Pred(f)` is the identity on `V` for the identity of the convex part `C₂`. -/
theorem stateLin_part_id (P : (dcSplitting σs separatedByStates).ε'.Part) :
    stateLin σs (𝟙 P : P ⟶ P).f = LinearMap.id :=
  gp_linearMap_ext fun a => by
    rw [stateLin_gmap, LinearMap.id_apply]
    congr 1; apply Subtype.ext
    show P.obj.p ≫ a.1 = a.1
    rw [(dcSplitting σs separatedByStates).ε'.prop P]
    show asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates) _ ≫ a.1 = a.1
    rw [asrtT_pred (orth_idem σs.hs), a.2]

/-- The predicate functor `C₂ → JB_npcᵒᵖ` of REC 102: `P ↦ V_P` (with
`Pred(P) ≅ [0,1]_{V_P}`), `f ↦ Pred(f)`. -/
noncomputable def rec102_jbFunctor :
    (dcSplitting σs separatedByStates).ε'.Part ⥤ JBnpcCat.{v}ᵒᵖ where
  obj P := Opposite.op (jbObj σs hRC h119 P.obj.X)
  map {P Q} f := Quiver.Hom.op ⟨stateLin σs f.f, stateLin_isNPC σs f.f⟩
  map_id P := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    exact stateLin_part_id σs P
  map_comp f g := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    exact stateLin_comp σs f.f g.f

theorem rec102_jbFunctor_map_eq {P Q : (dcSplitting σs separatedByStates).ε'.Part}
    (f g : P ⟶ Q) :
    (rec102_jbFunctor σs hRC h119).map f = (rec102_jbFunctor σs hRC h119).map g ↔
      ∀ q : Pred Q, f ≫ q = g ≫ q := by
  constructor
  · intro h q
    have h1 := congrArg Quiver.Hom.unop h
    have hl : stateLin σs f.f = stateLin σs g.f := congrArg Subtype.val h1
    apply KCat.hom_ext
    show f.f ≫ q.f = g.f ≫ q.f
    have hq : q.f ≫ orth σs.s = q.f := by
      have := KCat.comp_p q
      change q.f ≫ asrtT (orth σs.s) _ (effObj C) = q.f at this
      rwa [asrtT_effObj (orth_idem σs.hs)] at this
    have := congrArg (fun φ => φ (GP.gmap (cptMk σs (A := Q.obj.X) q.f hq))) hl
    simp only [stateLin_gmap] at this
    exact congrArg (fun x : CPt σs P.obj.X => x.1) (GP.gmap_injective this)
  · intro h
    apply Quiver.Hom.unop_inj; apply Subtype.ext
    refine gp_linearMap_ext fun a => ?_
    show stateLin σs f.f (GP.gmap a) = stateLin σs g.f (GP.gmap a)
    rw [stateLin_gmap, stateLin_gmap]
    congr 1; apply Subtype.ext
    have hQ : Q.obj.p = asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
        Q.obj.X := (dcSplitting σs separatedByStates).ε'.prop Q
    let qa : Pred Q := KCat.homMk a.1 (by
      show Q.obj.p ≫ a.1 ≫ asrtT (orth σs.s) _ (effObj C) = a.1
      rw [asrtT_effObj (orth_idem σs.hs), a.2, hQ, asrtT_pred (orth_idem σs.hs), a.2])
    exact congrArg Karoubi.Hom.f (h qa)

section PartSep

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))
  (hsep' : SeparatingStates C ∨ SeparatingPredicates C)

/-- In a part `C_t` (REC 92), maps that agree on the predicates of the part agree on
all predicates of `C`. -/
theorem part_pred_eq {P Q : (asrtIdem ht hsh hsep').Part} (f g : P ⟶ Q)
    (h : ∀ q : Pred Q, f ≫ q = g ≫ q) (b : Pred Q.obj.X) : f.f ≫ b = g.f ≫ b := by
  have hQ : Q.obj.p = asrtT t hsh Q.obj.X := (asrtIdem ht hsh hsep').prop Q
  have key : ∀ k : P ⟶ Q, k.f ≫ b = k.f ≫ (b ≫ t) := fun k => by
    calc k.f ≫ b = (k.f ≫ Q.obj.p) ≫ b := by rw [KCat.comp_p]
      _ = k.f ≫ (Q.obj.p ≫ b) := Category.assoc _ _ _
      _ = k.f ≫ (b ≫ t) := by rw [hQ, asrtT_pred ht hsh]
  let qb : Pred Q := KCat.homMk (b ≫ t) (by
    show Q.obj.p ≫ (b ≫ t) ≫ asrtT t hsh (effObj C) = b ≫ t
    rw [asrtT_effObj ht, Category.assoc b t t, ht, hQ, ← Category.assoc,
      asrtT_pred ht hsh, Category.assoc, ht])
  rw [key f, key g]
  exact congrArg Karoubi.Hom.f (h qb)

end PartSep

/-- For both parts, `Pred` separates the morphisms of the part exactly when
predicates of `C` separate the morphisms of `C` (the splitting of REC 95 is an
equivalence, and the predicates of a part are the corresponding part of `Pred`). -/
theorem parts_separated_iff :
    ((∀ {P Q : (dcSplitting σs separatedByStates).ε.Part} (f g : P ⟶ Q),
        (∀ q : Pred Q, f ≫ q = g ≫ q) → f = g) ∧
      (∀ {P Q : (dcSplitting σs separatedByStates).ε'.Part} (f g : P ⟶ Q),
        (∀ q : Pred Q, f ≫ q = g ≫ q) → f = g)) ↔ SeparatingPredicates C := by
  constructor
  · rintro ⟨h1, h2⟩ A B f g hfg
    apply (CentralSplitting.equivalence (dcSplitting σs separatedByStates)).functor.map_injective
    refine Prod.hom_ext (h1 _ _ fun q => KCat.hom_ext ?_) (h2 _ _ fun q => KCat.hom_ext ?_)
    · rw [KCat.comp_f, KCat.comp_f]
      exact (Category.assoc _ _ _).trans ((congrArg _ (hfg q.f)).trans (Category.assoc _ _ _).symm)
    · rw [KCat.comp_f, KCat.comp_f]
      exact (Category.assoc _ _ _).trans ((congrArg _ (hfg q.f)).trans (Category.assoc _ _ _).symm)
  · intro hs
    exact ⟨fun {P Q} f g h => KCat.hom_ext (hs _ _ fun b =>
        part_pred_eq σs.hs (isSharp_of_states σs.hs separatedByStates)
          (Or.inl separatedByStates) f g h b),
      fun {P Q} f g h => KCat.hom_ext (hs _ _ fun b =>
        part_pred_eq (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
          (Or.inl separatedByStates) f g h b)⟩

end Rec102


section Rec102Main

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

section PartLe

variable {t : Scal C} (ht : t ≫ t = t) (hsh : ∀ A : C, IsSharp (truth A ≫ t))
  (hsep' : SeparatingStates C ∨ SeparatingPredicates C)

/-- In a part `C_t`, the order of predicates is that of their underlying predicates
in `C` (through `partPredIso`). -/
theorem partPred_le_iff {P : (asrtIdem ht hsh hsep').Part} (a b : Pred P) :
    a ≼ b ↔ a.f ≼ b.f :=
  ((partPredIso ht hsh hsep' P).le_iff).trans (PredPart.le_iff ht)

end PartLe

theorem convexPart_pred_f (σs : ScalarSplit C) {P : (dcSplitting σs separatedByStates).ε'.Part}
    (q : Pred P) : q.f ≫ orth σs.s = q.f := by
  have := KCat.comp_p q
  change q.f ≫ asrtT (orth σs.s) _ (effObj C) = q.f at this
  rwa [asrtT_effObj (orth_idem σs.hs)] at this

theorem convexPart_homMk (σs : ScalarSplit C) (P : (dcSplitting σs separatedByStates).ε'.Part)
    (a : CPt σs P.obj.X) :
    P.obj.p ≫ a.1 ≫ (effObj (dcSplitting σs separatedByStates).ε'.Part).obj.p = a.1 := by
  show P.obj.p ≫ a.1 ≫ asrtT (orth σs.s) _ (effObj C) = a.1
  have hP : P.obj.p = asrtT (orth σs.s) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
      P.obj.X := (dcSplitting σs separatedByStates).ε'.prop P
  rw [asrtT_effObj (orth_idem σs.hs), a.2, hP, asrtT_pred (orth_idem σs.hs), a.2]

/-- `Pred(P) ≅ [0,1]_{V_P}` for an object `P` of the convex part `C₂` (the predicates
of `(A, asrt_{s⊥∘1})` are the convex part of `Pred(A)`, `partPredIso`, which is the
unit interval of its Gudder–Pulmannová space). -/
noncomputable def predEquivPart (σs : ScalarSplit C)
    (P : (dcSplitting σs separatedByStates).ε'.Part) :
    Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)) where
  toFun q := Papers.OAP.gpEquiv (CPt σs P.obj.X) (cptMk σs q.f (convexPart_pred_f σs q))
  invFun v := KCat.homMk ((Papers.OAP.gpEquiv (CPt σs P.obj.X)).symm v).1
    (convexPart_homMk σs P _)
  left_inv q := KCat.hom_ext (by
    dsimp only
    rw [KCat.homMk_f, Equiv.symm_apply_apply]; rfl)
  right_inv v := by
    show (Papers.OAP.gpEquiv (CPt σs P.obj.X)) (cptMk σs _ _) = v
    conv_rhs => rw [← (Papers.OAP.gpEquiv (CPt σs P.obj.X)).apply_symm_apply v]
    rfl

theorem predEquivPart_spec (σs : ScalarSplit C) (P : (dcSplitting σs separatedByStates).ε'.Part) :
    (∀ a b : Pred P, a ≼ b ↔ ((predEquivPart σs P a : VA σs P.obj.X) ≤ predEquivPart σs P b)) ∧
    (∀ (a b : Pred P) (h : Perp a b), (predEquivPart σs P (ovee a b h) : VA σs P.obj.X) =
      predEquivPart σs P a + predEquivPart σs P b) ∧
    (predEquivPart σs P (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X) := by
  refine ⟨fun a b => ?_, fun a b h => ?_, ?_⟩
  · show a ≼ b ↔ GP.gmap (cptMk σs a.f (convexPart_pred_f σs a)) ≤
      GP.gmap (cptMk σs b.f (convexPart_pred_f σs b))
    have h1 : (a.f : Pred P.obj.X) ≼ (b.f : Pred P.obj.X) ↔ cptMk σs a.f (convexPart_pred_f σs a) ≼
        cptMk σs b.f (convexPart_pred_f σs b) :=
      (PredPart.le_iff (orth_idem σs.hs) (A := P.obj.X) (p := cptMk σs a.f (convexPart_pred_f σs a))
        (q := cptMk σs b.f (convexPart_pred_f σs b))).symm
    exact (partPred_le_iff (orth_idem σs.hs) (isSharp_of_states (orth_idem σs.hs) separatedByStates)
      (Or.inl separatedByStates) a b).trans
        (h1.trans (Papers.OAP.gmap_le_gmap_iff (E := CPt σs P.obj.X)).symm)
  · show GP.gmap (cptMk σs (ovee a b h).f _) = GP.gmap (cptMk σs a.f _) + GP.gmap (cptMk σs b.f _)
    have hp : Perp (cptMk σs a.f (convexPart_pred_f σs a))
        (cptMk σs b.f (convexPart_pred_f σs b)) := h
    rw [← GP.gmap_ovee hp]
    rfl
  · show GP.gmap (cptMk σs (truth P).f _) = GP.gmap 1
    congr 1; apply Subtype.ext
    show P.obj.p ≫ truth P.obj.X = truth P.obj.X ≫ orth σs.s
    rw [(dcSplitting σs separatedByStates).ε'.prop P]
    exact asrtT_truth _ _

variable (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- **REC 102** (`thm:JB-embedding`, short.tex:1869, Theorem): a sequential effectus
`C` is equivalent to a product of effectuses `C₁ × C₂` where the predicate spaces of
`C₁` are complete Boolean algebras and those of `C₂` are (unit intervals of)
directed-complete JB-algebras; the predicate functors `C₁ → CBAᵒᵖ`,
`C₂ → JB_npcᵒᵖ` (`rec102_cbaFunctor`: `P ↦ Pred(P)`, `f ↦ Pred(f)`;
`rec102_jbFunctor`: `P ↦ V_P` with `Pred(P) ≅ [0,1]_{V_P}`, `f ↦ Pred(f)`) are
faithful iff `C` is separated by predicates.  The paper's proof: images (REC 106)
and compatible filters and comprehensions (REC 109) make REC 95 apply (the splitting
`dcSplitting` at the idempotent scalar of REC 35, with REC 34 = OAP 69); the Boolean
part is Boolean by REC 96–97, the convex part JB by REC 121.  Named hypotheses: the
Alfsen–Shultz results at REC 120 and 121, and REC 119 (citation-only in the print).
Cosmetic fixes of the print (PLAN flag 11): `JB_npc` (never defined in the print) is
JB-algebras with normal positive contractions, and the predicate spaces of `C₂` are
unit intervals of JB-algebras.  See `rec102_trivial_factor`: one of `C₁`, `C₂` is
always trivial. -/
theorem rec102 :
    ∃ σs : ScalarSplit C,
      Nonempty (C ≌ (dcSplitting σs separatedByStates).ε.Part ×
        (dcSplitting σs separatedByStates).ε'.Part) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε.Part, Nonempty (CBAOn (Pred P))) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε'.Part,
        ∃ _ : Mul (VA σs P.obj.X), JBAlgebra (VA σs P.obj.X) ∧
          IsDirectedCompleteOUS (VA σs P.obj.X) ∧
          ∃ e : Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)),
            (∀ a b : Pred P, a ≼ b ↔ (e a : VA σs P.obj.X) ≤ e b) ∧
            (∀ (a b : Pred P) (h : Perp a b), (e (ovee a b h) : VA σs P.obj.X) = e a + e b) ∧
            (e (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X)) ∧
      ((rec102_cbaFunctor σs).Faithful ∧ (rec102_jbFunctor σs hRC h119).Faithful ↔
        SeparatingPredicates C) := by
  obtain ⟨σs⟩ := scalarSplit_exists rec34_holds.{v} (normal (C := C)).1
  refine ⟨σs, ⟨CentralSplitting.equivalence _⟩, fun P => ⟨cbaOnPart σs P⟩, fun P => ?_, ?_⟩
  · exact ⟨jbMul σs hRC h119 P.obj.X, jbMul_spec σs hRC h119 P.obj.X, VA_dc σs _,
      predEquivPart σs P, predEquivPart_spec σs P⟩
  · rw [← parts_separated_iff σs, cbaPredFunctor_faithful_iff]
    apply and_congr_right'
    constructor
    · intro hF P Q f g h
      exact hF.map_injective ((rec102_jbFunctor_map_eq σs hRC h119 f g).2 h)
    · intro hs
      exact ⟨fun {P Q} {f g} h => hs f g ((rec102_jbFunctor_map_eq σs hRC h119 f g).1 h)⟩

/-- REC 102, addendum: in a sequential effectus one of the two factors of the
splitting is trivial — the idempotent scalar `s` of REC 35 is `0` or `1`, because
comprehensions and separation by (total) states leave no other idempotent scalars
(`idem_scalar_trivial`). -/
theorem rec102_trivial_factor (σs : ScalarSplit C) : σs.s = 0 ∨ σs.s = 𝟙 _ :=
  idem_scalar_trivial separatedByStates σs.hs

/-- **REC 104** (short.tex:1878, Remark) — **its claim is false**: the remark says
that for a sequential effectus "our scalars can satisfy `Pred(I) ≅ [0,1]_{C(X)}`
where `X` is an arbitrary Stonean space".  But the scalars of a sequential effectus
have no idempotents besides `0, 1` (`scal_irreducible_of_states`), whereas
`[0,1]_{C(X)}` has the idempotent indicator of a non-trivial clopen set as soon as
the extremally disconnected Hausdorff space `X` has two points.  So `X` has at most
one point, the scalars are `{0}`, `{0,1}` or `[0,1]` (REC 36), and every sequential
effectus has irreducible scalars: REC 102 is the case of REC 103. -/
theorem rec104_false (X : Type w) [TopologicalSpace X] [T2Space X]
    (hED : ExtremallyDisconnected X) {x y : X} (hxy : x ≠ y) :
    IsEmpty (@EMIso (Scal C) (Set.Icc (0 : C(X, ℝ)) 1) _
      (continuousUnitIntervalEffectMonoid X)) := by
  let _ := continuousUnitIntervalEffectMonoid X
  refine ⟨fun φ => ?_⟩
  have hirr := scal_irreducible_of_states (C := C) separatedByStates
  have hid := rec21_irreducible_iff.1 hirr
  -- a non-trivial clopen set
  obtain ⟨U, hU, hxU, hyU⟩ : ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
    obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := t2_separation hxy
    refine ⟨closure U, ⟨isClosed_closure, hED.open_closure U hUo⟩, subset_closure hxU, ?_⟩
    rw [mem_closure_iff]; push Not
    exact ⟨V, hVo, hyV, by rw [Set.inter_comm]; exact hUV.inter_eq⟩
  have hχ : kmul (kind U hU) (kind U hU) = kind U hU := kind_mul_self U hU
  have he : φ.inv.toFun (kind U hU) * φ.inv.toFun (kind U hU) = φ.inv.toFun (kind U hU) := by
    rw [← φ.inv.map_mul]; exact congrArg _ hχ
  rcases hid _ he with h | h
  · have := congrArg φ.hom.toFun h
    rw [φ.hom_inv, EffectMonoidHom.map_zero'] at this
    have h2 := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) x) this
    simp only [kind_apply, Set.indicator_of_mem hxU] at h2
    exact one_ne_zero h2
  · have := congrArg φ.hom.toFun h
    rw [φ.hom_inv, φ.hom.map_one] at this
    have h2 := congrArg (fun g : Set.Icc (0 : C(X, ℝ)) 1 => (g : C(X, ℝ)) y) this
    simp only [kind_apply, Set.indicator_of_notMem hyU] at h2
    exact zero_ne_one h2

end Rec102Main


/-! ### REC 103 -/

section Rec103

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- Irreducible scalars of a sequential effectus are `{0}`, `{0,1}` or `[0,1]`
(REC 36, `rec36_holds_rc`, applied to the directed-complete effect monoid `Pred(I)`). -/
theorem seq_scal_cases (hirr : IsIrreducible (Scal C)) :
    Subsingleton (Scal C) ∨ ScalarsAreTwo C ∨ IsRealEffectus C := by
  rcases rec36_holds_rc (Scal C) ((normal (C := C)).1 (effObj C)) hirr with h | h | h
  · exact Or.inl h
  · obtain ⟨φ⟩ := h; exact Or.inr (Or.inl ⟨φ.hom, φ.inv, φ.inv_hom, φ.hom_inv⟩)
  · obtain ⟨φ⟩ := h; exact Or.inr (Or.inr ⟨φ.hom, φ.inv, φ.inv_hom, φ.hom_inv⟩)

/-- With scalars `{0}` or `{0,1}` every predicate space is an orthoalgebra (REC 38). -/
theorem pred_isOrthoalgebra (h : Subsingleton (Scal C) ∨ ScalarsAreTwo C) (A : C) :
    IsOrthoalgebra (Pred A) := by
  rcases h with h | h
  · intro p _
    have h0 : (𝟙 (effObj C) : Scal C) = 0 := Subsingleton.elim _ _
    rw [← Category.comp_id p, h0, FinPAC.comp_zero]
  · exact rec38 separatedByStates h A

/-- An orthoalgebraic predicate space of a sequential effectus is a complete Boolean
algebra (REC 96, with completeness from directed completeness). -/
noncomputable def cbaOnPred (hOA : ∀ A : C, IsOrthoalgebra (Pred A)) (A : C) :
    CBAOn (Pred A) :=
  ⟨(rec96 (hOA A)).choose, fun a b => ((rec96 (hOA A)).choose_spec a b).1,
    boolean_complete_of_dc (rec96 (hOA A)).choose (fun a b => ((rec96 (hOA A)).choose_spec a b).1)
      ((normal (C := C)).1 A)⟩

/-- The splitting of real scalars `Pred(I) ≅ [0,1]`: `s = 0`, `c_λ = ψ(λ)`. -/
noncomputable def realSplit (ψ₀ : EffectMonoidHom I (Scal C)) : ScalarSplit C where
  s := 0
  hs := FinPAC.zero_comp _
  bool x hx _ := by rw [← hx, FinPAC.comp_zero]
  c := ψ₀.toFun
  c_mul l m := (ψ₀.map_mul l m).symm
  c_add l m h := ⟨ψ₀.perp_map (show Perp l m from h), (ψ₀.ovee_map (show Perp l m from h)).symm⟩
  c_one := by
    rw [ψ₀.map_one]; exact eabasics_orth_zero.symm

theorem orth_zero_scal : orth (0 : Scal C) = 𝟙 (effObj C) :=
  eabasics_orth_zero.trans scal_one_eq

/-- With `s = 0` the convex part is all of `Pred(A)`. -/
theorem cpt_all (σs : ScalarSplit C) (h0 : σs.s = 0) {A : C} (p : Pred A) :
    p ≫ orth σs.s = p := by
  rw [h0, orth_zero_scal, Category.comp_id]

variable (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

section JBW

variable (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

theorem realVal_hadd {a b : CPt (realSplit ψ₀) (effObj C)} (h : Perp a b) :
    ((φ₀.toFun (ovee a b h).1 : I) : ℝ) = ((φ₀.toFun a.1 : I) : ℝ) + ((φ₀.toFun b.1 : I) : ℝ) := by
  show ((φ₀.toFun (ovee a.1 b.1 h) : I) : ℝ) = _
  rw [φ₀.ovee_map h]; rfl

include h2 in
theorem realVal_hsmul (l : I) (a : CPt (realSplit ψ₀) (effObj C)) :
    ((φ₀.toFun (l • a).1 : I) : ℝ) = (l : ℝ) • ((φ₀.toFun a.1 : I) : ℝ) := by
  show ((φ₀.toFun (a.1 ≫ ψ₀.toFun l) : I) : ℝ) = (l : ℝ) • ((φ₀.toFun a.1 : I) : ℝ)
  rw [show a.1 ≫ ψ₀.toFun l = ψ₀.toFun l * a.1 from rfl, φ₀.map_mul, h2]
  rfl

/-- The real value `V_I → ℝ` of the scalars `Pred(I) ≅ [0,1]`. -/
noncomputable def realVal : VA (realSplit ψ₀) (effObj C) →ₗ[ℝ] ℝ :=
  gpLift (fun a => ((φ₀.toFun a.1 : I) : ℝ)) (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2)

theorem realVal_gmap (a : CPt (realSplit ψ₀) (effObj C)) :
    realVal φ₀ ψ₀ h2 (GP.gmap a) = ((φ₀.toFun a.1 : I) : ℝ) :=
  gpLift_gmap _ (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2) a

theorem realVal_unit : realVal φ₀ ψ₀ h2 GP.gunit = 1 := by
  show realVal φ₀ ψ₀ h2 (GP.gmap 1) = 1
  rw [realVal_gmap]
  show ((φ₀.toFun (truth (effObj C) ≫ orth 0) : I) : ℝ) = 1
  rw [orth_zero_scal, Category.comp_id, truth_effObj_eq_id, ← scal_one_eq, φ₀.map_one]; rfl

theorem realVal_nonneg {v : VA (realSplit ψ₀) (effObj C)} (hv : 0 ≤ v) :
    0 ≤ realVal φ₀ ψ₀ h2 v :=
  gpLift_nonneg (E := CPt (realSplit ψ₀) (effObj C))
    (fun a : CPt (realSplit ψ₀) (effObj C) => ((φ₀.toFun a.1 : I) : ℝ))
    (realVal_hadd φ₀ ψ₀) (realVal_hsmul φ₀ ψ₀ h2)
    (fun a : CPt (realSplit ψ₀) (effObj C) => (φ₀.toFun a.1).2.1) hv

theorem realVal_mono : Monotone (realVal φ₀ ψ₀ h2) := fun v w hvw => by
  have := realVal_nonneg φ₀ ψ₀ h2 (sub_nonneg.2 hvw); rwa [map_sub, sub_nonneg] at this

/-- `x ≼ y` in `[0,1]` iff `x ≤ y`. -/
theorem unitInterval_le_iff (x y : I) : x ≼ y ↔ (x : ℝ) ≤ y := by
  constructor
  · rintro ⟨c, _, rfl⟩; show (x : ℝ) ≤ x + c; linarith [c.2.1]
  · intro h
    refine ⟨⟨(y : ℝ) - x, by linarith, by linarith [y.2.2, x.2.1]⟩, ?_, Subtype.ext ?_⟩
    · show (x : ℝ) + ((y : ℝ) - x) ≤ 1; linarith [y.2.2]
    · show (x : ℝ) + ((y : ℝ) - x) = y; ring

theorem gmap_half (A : C) :
    GP.gmap (Papers.OAP.ihalf • (1 : CPt (realSplit ψ₀) A)) =
      (1 / 2 : ℝ) • (GP.gunit : VA (realSplit ψ₀) A) := by
  rw [GP.gmap_smul]; rfl

/-- Effect monoid morphisms are monotone (as `Papers.OAP.emHom_monotone`, not imported). -/
theorem emHom_mono_loc {M : Type*} {N : Type*} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) {a b : M} (h : a ≼ b) : f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hac, rfl⟩ := Papers.OAP.le_def.1 h
  exact Papers.OAP.le_def.2 ⟨f.toFun c, f.perp_map hac, by
    rw [Papers.OAP.oplus_eq (f.perp_map hac), Papers.OAP.oplus_eq hac, f.ovee_map hac]⟩

include h1 in
/-- The real value reflects the order: `V_I ≅ ℝ`. -/
theorem realVal_le_iff (v w : VA (realSplit ψ₀) (effObj C)) :
    realVal φ₀ ψ₀ h2 v ≤ realVal φ₀ ψ₀ h2 w ↔ v ≤ w := by
  refine ⟨fun h => ?_, fun h => realVal_mono φ₀ ψ₀ h2 h⟩
  rw [← sub_nonneg] at h ⊢
  rw [← map_sub] at h
  obtain ⟨N, a, hN, e⟩ := gp_affine_repr (w - v)
  rw [e] at h ⊢
  rw [map_sub, map_smul, map_smul, realVal_gmap, realVal_unit] at h
  have ha : (1 / 2 : ℝ) ≤ φ₀.toFun a.1 := by
    simp only [smul_eq_mul, mul_one] at h; nlinarith
  set half : CPt (realSplit ψ₀) (effObj C) := Papers.OAP.ihalf • (1 : CPt _ _) with hhdef
  have hhalf : ((φ₀.toFun half.1 : I) : ℝ) = 1 / 2 := by
    show ((φ₀.toFun ((truth (effObj C) ≫ orth 0) ≫ ψ₀.toFun Papers.OAP.ihalf) : I) : ℝ) = _
    rw [orth_zero_scal, Category.comp_id, truth_effObj_eq_id, Category.id_comp, h2]; rfl
  have hs : φ₀.toFun half.1 ≼ φ₀.toFun a.1 :=
    (unitInterval_le_iff _ _).2 (by rw [hhalf]; exact ha)
  have hs' := emHom_mono_loc ψ₀ hs
  rw [h1, h1] at hs'
  have hle : half ≼ a := (PredPart.le_iff _).2 hs'
  have := gmap_mono hle
  rw [hhdef, gmap_half] at this
  have h3 : (2 * N) • ((1 / 2 : ℝ) • (GP.gunit : VA (realSplit ψ₀) (effObj C))) ≤
      (2 * N) • GP.gmap a := ou_smul_le_smul (by positivity) this
  rw [_root_.smul_smul, show 2 * N * (1 / 2) = N by ring] at h3
  exact sub_nonneg.2 h3

include h1 in
theorem realVal_normal : IsNormalMap (realVal φ₀ ψ₀ h2) := by
  intro S s _ _ hs
  refine ⟨by rintro _ ⟨x, hx, rfl⟩; exact realVal_mono φ₀ ψ₀ h2 (hs.1 hx), fun t ht => ?_⟩
  have htv : realVal φ₀ ψ₀ h2 (t • GP.gunit) = t := by
    rw [map_smul, realVal_unit, smul_eq_mul, mul_one]
  have hs' : s ≤ t • (GP.gunit : VA (realSplit ψ₀) (effObj C)) :=
    hs.2 fun x hx => (realVal_le_iff φ₀ ψ₀ h1 h2 _ _).1 (by rw [htv]; exact ht ⟨x, hx, rfl⟩)
  have := realVal_mono φ₀ ψ₀ h2 hs'
  rwa [htv] at this

/-- The normal state `a ↦ ω(a)` of `V_A` for a state `ω` of the effectus
(REC 103's "these correspond to normal states `ω* : V_A → ℝ`"). -/
noncomputable def normalState {A : C} (ω : Stat A) : OUSState (VA (realSplit ψ₀) A) where
  toLin := realVal φ₀ ψ₀ h2 ∘ₗ stateLin (realSplit ψ₀) ω.1
  nonneg a ha := realVal_nonneg φ₀ ψ₀ h2 (stateLin_nonneg _ ω.1 ha)
  unital := by
    rw [LinearMap.comp_apply]
    have : stateLin (realSplit ψ₀) ω.1 (ouUnit (VA (realSplit ψ₀) A)) = GP.gunit := by
      show stateLin _ ω.1 (GP.gmap 1) = GP.gmap 1
      rw [stateLin_gmap]; congr 1; apply Subtype.ext
      show ω.1 ≫ (truth A ≫ orth 0) = truth (effObj C) ≫ orth 0
      rw [← Category.assoc, ω.2]
    rw [this, realVal_unit]

include h1 in
theorem normalState_normal {A : C} (ω : Stat A) :
    IsNormalMap (normalState φ₀ ψ₀ h2 ω).toLin := by
  intro S s hne hdir hs
  have e1 := stateLin_normal (realSplit ψ₀) ω.1 S s hne hdir hs
  have e2 := realVal_normal φ₀ ψ₀ h1 h2 _ _ (hne.image _)
    (hdir.mono_comp (monotone_of_pos fun _ hv => stateLin_nonneg _ ω.1 hv)) e1
  rw [Set.image_image] at e2
  exact e2

include h1 h2 in
/-- With `Pred(I) ≅ [0,1]`, the normal states of the effectus separate `V_A`: it is a
JBW-algebra (REC 48) once it is a JB-algebra. -/
theorem separating_normal_states (A : C) :
    HasSeparatingNormalStates (VA (realSplit ψ₀) A) := by
  intro v w hvw
  obtain ⟨N, a, hN, e⟩ := gp_affine_repr (v - w)
  set half : CPt (realSplit ψ₀) A := Papers.OAP.ihalf • (1 : CPt _ _) with hhdef
  have hne : a.1 ≠ half.1 := by
    intro h
    have : a = half := Subtype.ext h
    apply hvw
    rw [← sub_eq_zero, e, this, hhdef, gmap_half, _root_.smul_smul,
      show 2 * N * (1 / 2) = N by ring, sub_self]
  obtain ⟨ω, hω⟩ : ∃ ω : Stat A, ω.1 ≫ a.1 ≠ ω.1 ≫ half.1 := by
    by_contra hc; push Not at hc
    exact hne (separatedByStates _ _ hc)
  refine ⟨normalState φ₀ ψ₀ h2 ω, normalState_normal φ₀ ψ₀ h1 h2 ω, fun heq => ?_⟩
  have h0 : (normalState φ₀ ψ₀ h2 ω).toLin (v - w) = 0 := by rw [map_sub, heq, sub_self]
  have hu : (normalState φ₀ ψ₀ h2 ω).toLin GP.gunit = 1 := (normalState φ₀ ψ₀ h2 ω).unital
  rw [e, map_sub, map_smul, map_smul, hu] at h0
  have hga : (normalState φ₀ ψ₀ h2 ω).toLin (GP.gmap a) = ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) := by
    show realVal φ₀ ψ₀ h2 (stateLin _ ω.1 (GP.gmap a)) = _
    rw [stateLin_gmap, realVal_gmap]; rfl
  rw [hga] at h0
  have hhalf : ((φ₀.toFun (ω.1 ≫ half.1) : I) : ℝ) = 1 / 2 := by
    show ((φ₀.toFun (ω.1 ≫ ((truth A ≫ orth 0) ≫ ψ₀.toFun Papers.OAP.ihalf)) : I) : ℝ) = _
    rw [← Category.assoc, ← Category.assoc, ω.2, orth_zero_scal, Category.comp_id,
      truth_effObj_eq_id, Category.id_comp, h2]; rfl
  apply hω
  have h3 : ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) = ((φ₀.toFun (ω.1 ≫ half.1) : I) : ℝ) := by
    rw [hhalf]; simp only [smul_eq_mul, mul_one] at h0
    have : (2 * N) * ((φ₀.toFun (ω.1 ≫ a.1) : I) : ℝ) = N := by linarith
    field_simp at this ⊢; nlinarith
  have h4 : φ₀.toFun (ω.1 ≫ a.1) = φ₀.toFun (ω.1 ≫ half.1) := Subtype.ext h3
  rw [← h1 (ω.1 ≫ a.1), h4, h1]

end JBW

/-- `V_A` as an object of `JBW_npc`. -/
noncomputable def jbwObj (σs : ScalarSplit C)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A)) (A : C) :
    JBWnpcCat.{v} :=
  @JBWnpcCat.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (hJBW A)

theorem stateLin_id (σs : ScalarSplit C) (A : C) : stateLin σs (𝟙 A) = LinearMap.id :=
  gp_linearMap_ext fun a => by
    rw [stateLin_gmap, LinearMap.id_apply]; congr 1; exact Subtype.ext (Category.id_comp _)

/-- The predicate functor `C → JBW_npcᵒᵖ` of REC 103 (`A ↦ V_A`, `f ↦ Pred(f)`). -/
noncomputable def rec103_jbwFunctor (σs : ScalarSplit C)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A)) :
    C ⥤ JBWnpcCat.{v}ᵒᵖ where
  obj A := Opposite.op (jbwObj hRC h119 σs hJBW A)
  map f := Quiver.Hom.op ⟨stateLin σs f, stateLin_isNPC σs f⟩
  map_id A := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_id σs A
  map_comp f g := by
    apply Quiver.Hom.unop_inj; apply Subtype.ext; exact stateLin_comp σs f g

theorem rec103_jbwFunctor_faithful_iff (σs : ScalarSplit C) (h0 : σs.s = 0)
    (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A)) :
    (rec103_jbwFunctor hRC h119 σs hJBW).Faithful ↔ SeparatingPredicates C := by
  have key : ∀ {A B : C} (f g : A ⟶ B), (rec103_jbwFunctor hRC h119 σs hJBW).map f =
      (rec103_jbwFunctor hRC h119 σs hJBW).map g ↔ ∀ b : Pred B, f ≫ b = g ≫ b := by
    intro A B f g
    constructor
    · intro h b
      have hl : stateLin σs f = stateLin σs g :=
        congrArg Subtype.val (congrArg Quiver.Hom.unop h)
      have := congrArg (fun φ => φ (GP.gmap (cptMk σs (A := B) b (cpt_all σs h0 b)))) hl
      simp only [stateLin_gmap] at this
      exact congrArg (fun x : CPt σs A => x.1) (GP.gmap_injective this)
    · intro h
      apply Quiver.Hom.unop_inj; apply Subtype.ext
      refine gp_linearMap_ext fun a => ?_
      show stateLin σs f (GP.gmap a) = stateLin σs g (GP.gmap a)
      rw [stateLin_gmap, stateLin_gmap]; congr 1; exact Subtype.ext (h a.1)
  constructor
  · intro hF A B f g h
    exact hF.map_injective ((key f g).2 h)
  · intro hs
    exact ⟨fun {A B} {f g} h => hs f g ((key f g).1 h)⟩

/-- **REC 103** (`thm:JBW-CBA`, short.tex:1874, Theorem): a sequential effectus with
irreducible scalars has either all predicate spaces complete Boolean algebras, or all
of them unit intervals of JBW-algebras; the predicate functor `C → CBAᵒᵖ` resp.
`C → JBW_npcᵒᵖ` is faithful iff `C` is separated by predicates.  The paper's proof:
the scalars are `{0}`, `{0,1}` or `[0,1]` (REC 36, discharged here through REC 34 =
OAP 69); in the first two cases the predicate spaces are orthoalgebras (REC 38), hence
complete Boolean algebras (REC 96); with `[0,1]` scalars they are unit intervals of
directed-complete JB-algebras (REC 121), and the effectus's states give normal states
of `V_A` separating it, so `V_A` is JBW.  Named hypotheses as for REC 102.  (The
irreducibility hypothesis is automatic, `scal_irreducible_of_states`; "CBA *of*
JBW_npc" is read "CBA *or* JBW_npc", PLAN flag 11.) -/
theorem rec103 (hirr : IsIrreducible (Scal C)) :
    (∃ hB : ∀ A : C, CBAOn (Pred A), (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates C) ∨
    (∃ (σs : ScalarSplit C) (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A)),
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : VA σs A) (ouUnit (VA σs A)),
        (∀ a b : Pred A, a ≼ b ↔ (e a : VA σs A) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b), (e (ovee a b h) : VA σs A) = e a + e b) ∧
        (e (truth A) : VA σs A) = ouUnit (VA σs A)) ∧
      ((rec103_jbwFunctor hRC h119 σs hJBW).Faithful ↔ SeparatingPredicates C)) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · exact Or.inl ⟨cbaOnPred (pred_isOrthoalgebra (Or.inl h)), cbaPredFunctor_faithful_iff _⟩
  · exact Or.inl ⟨cbaOnPred (pred_isOrthoalgebra (Or.inr h)), cbaPredFunctor_faithful_iff _⟩
  · right
    set σs := realSplit ψ₀ with hσs
    have h0 : σs.s = 0 := rfl
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) := fun A =>
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (jbMul_spec σs hRC h119 A)
        (VA_dc σs A) (separating_normal_states φ₀ ψ₀ h1 h2 A)
    refine ⟨σs, hJBW, fun A => ?_, rec103_jbwFunctor_faithful_iff hRC h119 σs h0 hJBW⟩
    let e₁ : Pred A ≃ CPt σs A :=
      ⟨fun p => cptMk σs p (cpt_all σs h0 p), fun q => q.1, fun _ => rfl, fun _ => rfl⟩
    refine ⟨e₁.trans (Papers.OAP.gpEquiv (CPt σs A)), fun a b => ?_, fun a b h => ?_, ?_⟩
    · exact (PredPart.le_iff (orth_idem σs.hs) (p := cptMk σs a (cpt_all σs h0 a))
        (q := cptMk σs b (cpt_all σs h0 b))).symm.trans
          (Papers.OAP.gmap_le_gmap_iff (E := CPt σs A)).symm
    · show GP.gmap (cptMk σs (ovee a b h) _) = GP.gmap (cptMk σs a _) + GP.gmap (cptMk σs b _)
      have hp : Perp (cptMk σs a (cpt_all σs h0 a)) (cptMk σs b (cpt_all σs h0 b)) := h
      rw [← GP.gmap_ovee hp]; rfl
    · show GP.gmap (cptMk σs (truth A) _) = GP.gmap 1
      congr 1; apply Subtype.ext
      show truth A = truth A ≫ orth σs.s
      rw [cpt_all σs h0]

end Rec103

end Papers.REC
