/-
Papers/SIG/Convex.lean

SIG §5.2 "Probabilistic models" (main.tex:1452–1690) and its proofs in
Appendix C (main.tex:3025–3462): the convex σ-effectuses, points SIG 51–61
and SIG 68–73 (printed numbers).

Design:
* An ordered vector space with order unit is the tree's `OrderUnitSpace`
  mixin (SIG 51; `ouUnit_isOrderUnitPrinted` and OAP 58's `oap58_ofPaper`
  match it with the printed definition).  `OVSu` bundles it, with subunital
  positive linear maps.
* `EMod[M]` (finite) is `EModS M` here: effect modules and additive
  action-preserving maps.  (`Papers/SIG/Finite.lean`, written in parallel,
  has the same category as `EMod`; the two can be merged once both are
  importable.)
* `[0,u]_A` is the tree's `orderIntervalEffectAlgebra`/`Module` through OAP's
  `ousEA`/`ousEMod`; the inverse of `A ↦ [0,u]_A` is the Gudder–Pulmannová
  space `GP.Vec E` of the tree (179III.2).
* SIG 52 is proved (the print cites [JacobsMF16]): fullness by extending an
  affine map `[0,u]_A → [0,u]_B` to `F x = 2m·h((x + m u)/2m) - m·h(u)`.
* The σ-effectus structure of `sBOUSᵒᵖ` (and of `sBBNS`) is transported from
  `sEMod[[0,1]]ᵒᵖ` (`sWMod[[0,1]]`) along the equivalence, by a generic
  construction (`SumsCompatible.sigmaEffectus`); SIG 56 and SIG 60 lift the
  morphisms `Pred` and `sSt` through it (`liftMorphism`), after restricting
  scalars along `C(I,I) ≅ [0,1]` (`restrictMorphism`, `restrictSWMorphism`).
  They are stated for small `C` (`C : Type`), the universe of `sBOUS`.
-/
import Papers.SIG.WeightModules
import Papers.OAP.OUS
import Theses.B.Eff.Quotients

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite
open scoped unitInterval

namespace Papers.SIG

open SigmaPAM

universe u v u₂ v₂ u₃ v₃

/-! ## The unit interval `[0,u]_V` of an ordered vector space with order unit -/

section Ivl

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- `[0,u]_V`. -/
abbrev Ivl (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] :
    Type u := Set.Icc (0 : V) (ouUnit V)

theorem ivl_perp_iff {a b : Ivl V} : Perp a b ↔ (a : V) + b ≤ ouUnit V := Iff.rfl

theorem ivl_ovee_coe {a b : Ivl V} (h : Perp a b) : ((ovee a b h : Ivl V) : V) = a + b := rfl

theorem ivl_smul_coe (r : I) (a : Ivl V) : ((r • a : Ivl V) : V) = (r : ℝ) • (a : V) := rfl

theorem ivl_zero_coe : ((0 : Ivl V) : V) = 0 := rfl

theorem ivl_one_coe : ((1 : Ivl V) : V) = ouUnit V := rfl

theorem ivl_le_iff {a b : Ivl V} : a ≼ b ↔ (a : V) ≤ b :=
  Papers.OAP.oap3_le_iff V (ouUnit V) ou_unit_nonneg a b

end Ivl


/-! ## The extension of an affine map on `[0,u]` to a linear map -/

section Extension

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

open Classical in
/-- An element of `V` clamped into `[0,u]` (the value `0` outside). -/
noncomputable def clampI (v : V) : Ivl V :=
  if h : 0 ≤ v ∧ v ≤ ouUnit V then ⟨v, h⟩ else 0

theorem clampI_coe {v : V} (h0 : 0 ≤ v) (h1 : v ≤ ouUnit V) : ((clampI v : Ivl V) : V) = v := by
  rw [clampI, dite_eq_left_of_eq_true (eq_true ⟨h0, h1⟩)]

/-- `m` is a valid scale for `x`: `-m·u ≤ x ≤ m·u`. -/
def ValidScale (m : ℝ) (x : V) : Prop := -(m • ouUnit V) ≤ x ∧ x ≤ m • ouUnit V

theorem ValidScale.mono {m m' : ℝ} {x : V} (h : ValidScale m x) (hm : m ≤ m') :
    ValidScale m' x :=
  ⟨le_trans (neg_le_neg (ou_smul_unit_mono hm)) h.1, h.2.trans (ou_smul_unit_mono hm)⟩

theorem exists_validScale (x : V) : ∃ n : ℕ, ValidScale ((n : ℝ) + 1) x := by
  obtain ⟨n, h1, h2⟩ := Papers.OAP.oap58_orderUnit x
  exact ⟨n, ValidScale.mono ⟨h1, h2⟩ (by linarith)⟩

theorem validScale_mem {m : ℝ} (hm : 0 < m) {x : V} (h : ValidScale m x) :
    0 ≤ (2 * m)⁻¹ • (x + m • ouUnit V) ∧ (2 * m)⁻¹ • (x + m • ouUnit V) ≤ ouUnit V := by
  have hc : (0 : ℝ) ≤ (2 * m)⁻¹ := by positivity
  constructor
  · exact ou_smul_nonneg hc (by have := h.1; rw [← sub_nonneg, sub_neg_eq_add] at this; exact this)
  · have : x + m • ouUnit V ≤ (2 * m) • ouUnit V := by
      have := add_le_add_right h.2 (m • ouUnit V)
      rwa [← add_smul, show m + m = 2 * m by ring, add_comm (m • ouUnit V)] at this
    calc (2 * m)⁻¹ • (x + m • ouUnit V) ≤ (2 * m)⁻¹ • ((2 * m) • ouUnit V) :=
          ou_smul_le_smul hc this
      _ = ouUnit V := by rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- An **affine** map `[0,u]_V → [0,u]_W`: additive and `[0,1]`-homogeneous,
stated on the underlying vectors. -/
structure IsAffineIvl (h : Ivl V → Ivl W) : Prop where
  map_zero : ((h 0 : Ivl W) : W) = 0
  map_add : ∀ (a b : Ivl V) (hab : Perp a b), ((h (ovee a b hab)) : W) = h a + h b
  map_smul : ∀ (r : I) (a : Ivl V), ((h (r • a)) : W) = (r : ℝ) • (h a : W)

theorem isAffineIvl_of {h : Ivl V → Ivl W} (hadd : IsAdditive h)
    (hsm : ∀ (r : I) (a : Ivl V), h (r • a) = r • h a) : IsAffineIvl h where
  map_zero := congrArg Subtype.val hadd.1
  map_add a b hab := by
    obtain ⟨h', e⟩ := hadd.2 hab
    rw [← e]; rfl
  map_smul r a := by rw [hsm]; rfl

variable {h : Ivl V → Ivl W}

/-- Convex combinations: `h (r a + s b) = r h a + s h b` for `r + s ≤ 1`. -/
theorem IsAffineIvl.convex (hh : IsAffineIvl h) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hr1 : r ≤ 1) (hs1 : s ≤ 1) (a b z : Ivl V) (hz : (z : V) = r • (a : V) + s • (b : V)) :
    (h z : W) = r • (h a : W) + s • (h b : W) := by
  have hp : Perp (GP.Iv r • a) (GP.Iv s • b) := by
    rw [ivl_perp_iff, ivl_smul_coe, ivl_smul_coe, GP.Iv_coe hr hr1, GP.Iv_coe hs hs1, ← hz]
    exact z.2.2
  have ez : z = ovee (GP.Iv r • a) (GP.Iv s • b) hp := by
    apply Subtype.ext
    rw [ivl_ovee_coe, ivl_smul_coe, ivl_smul_coe, GP.Iv_coe hr hr1, GP.Iv_coe hs hs1, hz]
  rw [ez, hh.map_add, hh.map_smul, hh.map_smul, GP.Iv_coe hr hr1, GP.Iv_coe hs hs1]

/-- The candidate value `2m · h((x + m u)/2m) - m · h(u)`. -/
noncomputable def extG (h : Ivl V → Ivl W) (m : ℝ) (x : V) : W :=
  (2 * m) • (h (clampI ((2 * m)⁻¹ • (x + m • ouUnit V))) : W) - m • (h 1 : W)

theorem extG_le (hh : IsAffineIvl h) {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') {x : V}
    (hx : ValidScale m x) : extG h m x = extG h m' x := by
  have hm' : 0 < m' := lt_of_lt_of_le hm hmm
  have hx' := hx.mono hmm
  obtain ⟨a0, a1⟩ := validScale_mem hm hx
  obtain ⟨b0, b1⟩ := validScale_mem hm' hx'
  have key := hh.convex (r := m / m') (s := (m' - m) / (2 * m')) (by positivity)
    (div_nonneg (by linarith) (by positivity)) ((div_le_one hm').2 hmm)
    (by rw [div_le_one (by positivity)]; linarith)
    (clampI ((2 * m)⁻¹ • (x + m • ouUnit V))) 1 (clampI ((2 * m')⁻¹ • (x + m' • ouUnit V)))
    (by
      rw [clampI_coe b0 b1, clampI_coe a0 a1, ivl_one_coe]
      match_scalars <;> (field_simp; try ring))
  unfold extG
  rw [key]
  match_scalars <;> (field_simp; try ring)

theorem extG_eq (hh : IsAffineIvl h) {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m') {x : V}
    (hx : ValidScale m x) (hx' : ValidScale m' x) : extG h m x = extG h m' x := by
  rcases le_total m m' with hmm | hmm
  · exact extG_le hh hm hmm hx
  · exact (extG_le hh hm' hmm hx').symm

/-- The extension `F : V → W` of `h`. -/
noncomputable def extF (h : Ivl V → Ivl W) (x : V) : W :=
  extG h ((exists_validScale x).choose + 1) x

theorem extF_eq (hh : IsAffineIvl h) {m : ℝ} (hm : 0 < m) {x : V} (hx : ValidScale m x) :
    extF h x = extG h m x :=
  extG_eq hh (by positivity) hm (exists_validScale x).choose_spec hx

theorem extF_add (hh : IsAffineIvl h) (x y : V) : extF h (x + y) = extF h x + extF h y := by
  obtain ⟨n, hn⟩ := exists_validScale x
  obtain ⟨k, hk⟩ := exists_validScale y
  set m : ℝ := (n : ℝ) + 1 + ((k : ℝ) + 1)
  have hm : 0 < m := by positivity
  have hxm : ValidScale m x := hn.mono (by simp only [m]; linarith)
  have hym : ValidScale m y := hk.mono (by simp only [m]; linarith)
  have hxy : ValidScale (2 * m) (x + y) := by
    refine ⟨?_, ?_⟩
    · rw [two_mul, add_smul, neg_add]; exact add_le_add hxm.1 hym.1
    · rw [two_mul, add_smul]; exact add_le_add hxm.2 hym.2
  rw [extF_eq hh (by positivity) hxy, extF_eq hh hm hxm, extF_eq hh hm hym]
  obtain ⟨a0, a1⟩ := validScale_mem hm hxm
  obtain ⟨b0, b1⟩ := validScale_mem hm hym
  obtain ⟨c0, c1⟩ := validScale_mem (by positivity : (0:ℝ) < 2 * m) hxy
  have key := hh.convex (r := 1 / 2) (s := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (clampI ((2 * m)⁻¹ • (x + m • ouUnit V))) (clampI ((2 * m)⁻¹ • (y + m • ouUnit V)))
    (clampI ((2 * (2 * m))⁻¹ • (x + y + (2 * m) • ouUnit V)))
    (by
      rw [clampI_coe c0 c1, clampI_coe a0 a1, clampI_coe b0 b1]
      match_scalars <;> (field_simp; try ring))
  unfold extG
  rw [key]
  match_scalars <;> ring

theorem validScale_one {a : V} (h0 : 0 ≤ a) (h1 : a ≤ ouUnit V) : ValidScale 1 a :=
  ⟨by rw [one_smul]; exact (neg_nonpos.2 ou_unit_nonneg).trans h0, by rwa [one_smul]⟩

/-- The extension restricts to `h`. -/
theorem extF_ivl (hh : IsAffineIvl h) (a : Ivl V) : extF h (a : V) = (h a : W) := by
  rw [extF_eq hh one_pos (validScale_one a.2.1 a.2.2)]
  obtain ⟨c0, c1⟩ := validScale_mem one_pos (validScale_one a.2.1 a.2.2)
  have key := hh.convex (r := 1 / 2) (s := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a 1 (clampI (((2 : ℝ) * 1)⁻¹ • ((a : V) + (1 : ℝ) • ouUnit V)))
    (by rw [clampI_coe c0 c1, ivl_one_coe]; match_scalars <;> norm_num)
  unfold extG
  rw [key]
  match_scalars <;> norm_num

theorem extF_zero (hh : IsAffineIvl h) : extF h (0 : V) = 0 := by
  have := extF_ivl hh (0 : Ivl V)
  rwa [ivl_zero_coe, hh.map_zero] at this

theorem extF_smul_unit (hh : IsAffineIvl h) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : V) :
    extF h (c • x) = c • extF h x := by
  obtain ⟨n, hn⟩ := exists_validScale x
  set m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by positivity
  have hcx : ValidScale m (c • x) := by
    refine ⟨?_, ?_⟩
    · have := ou_smul_le_smul hc0 hn.1
      rw [smul_neg, smul_smul] at this
      refine le_trans (neg_le_neg ?_) this
      exact ou_smul_unit_mono (by nlinarith)
    · have := ou_smul_le_smul hc0 hn.2
      rw [smul_smul] at this
      exact this.trans (ou_smul_unit_mono (by nlinarith))
  rw [extF_eq hh hm hcx, extF_eq hh hm hn]
  obtain ⟨a0, a1⟩ := validScale_mem hm hn
  obtain ⟨c0, c1⟩ := validScale_mem hm hcx
  have key := hh.convex (r := c) (s := (1 - c) / 2) hc0 (by linarith) hc1 (by linarith)
    (clampI ((2 * m)⁻¹ • (x + m • ouUnit V))) 1 (clampI ((2 * m)⁻¹ • (c • x + m • ouUnit V)))
    (by
      rw [clampI_coe c0 c1, clampI_coe a0 a1, ivl_one_coe]
      match_scalars <;> (field_simp; try ring))
  unfold extG
  rw [key]
  match_scalars <;> ring

/-- An additive map of real vector spaces that is homogeneous for scalars in
`[0,1]` is linear. -/
theorem linear_of_unit_homogeneous {F : V → W} (hadd : ∀ x y, F (x + y) = F x + F y)
    (hsm : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ x, F (c • x) = c • F x) (c : ℝ) (x : V) :
    F (c • x) = c • F x := by
  have h0 : F 0 = 0 := by
    have := hadd 0 0; rw [add_zero] at this
    exact left_eq_add.1 this
  have hneg : ∀ y, F (-y) = -F y := fun y => by
    have := hadd y (-y); rw [add_neg_cancel, h0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hpos : ∀ c : ℝ, 0 ≤ c → ∀ x, F (c • x) = c • F x := by
    intro c hc x
    rcases le_or_gt c 1 with h1 | h1
    · exact hsm c hc h1 x
    · have hc' : 0 < c := by linarith
      have := hsm c⁻¹ (by positivity) (inv_le_one_of_one_le₀ h1.le) (c • x)
      rw [smul_smul, inv_mul_cancel₀ hc'.ne', one_smul] at this
      rw [this, smul_smul, mul_inv_cancel₀ hc'.ne', one_smul]
  rcases le_or_gt 0 c with hc | hc
  · exact hpos c hc x
  · have := hpos (-c) (by linarith) x
    rw [show c • x = -((-c) • x) by rw [neg_smul, neg_neg], hneg, this, neg_smul, neg_neg]

/-- The extension as a linear map. -/
noncomputable def extLin (hh : IsAffineIvl h) : V →ₗ[ℝ] W where
  toFun := extF h
  map_add' := extF_add hh
  map_smul' c x := linear_of_unit_homogeneous (extF_add hh)
    (fun c hc0 hc1 x => extF_smul_unit hh hc0 hc1 x) c x

theorem extLin_apply (hh : IsAffineIvl h) (x : V) : extLin hh x = extF h x := rfl

theorem extLin_nonneg (hh : IsAffineIvl h) {x : V} (hx : 0 ≤ x) : 0 ≤ extLin hh x := by
  rw [extLin_apply]
  obtain ⟨n, hn⟩ := exists_validScale x
  set m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by positivity
  rw [extF_eq hh hm hn]
  obtain ⟨a0, a1⟩ := validScale_mem hm hn
  have b0 : 0 ≤ (2 * m)⁻¹ • x := ou_smul_nonneg (by positivity) hx
  have b1 : (2 * m)⁻¹ • x ≤ ouUnit V := by
    have := ou_smul_le_smul (show (0:ℝ) ≤ (2 * m)⁻¹ by positivity) hn.2
    refine this.trans ?_
    rw [smul_smul]
    exact (ou_smul_unit_mono (show (2 * m)⁻¹ * m ≤ 1 by rw [inv_mul_le_iff₀ (by positivity)]; linarith)).trans
      (by rw [one_smul])
  have key := hh.convex (r := 1) (s := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (clampI ((2 * m)⁻¹ • x)) 1 (clampI ((2 * m)⁻¹ • (x + m • ouUnit V)))
    (by
      rw [clampI_coe a0 a1, clampI_coe b0 b1, ivl_one_coe]
      match_scalars <;> (field_simp; try ring))
  unfold extG
  rw [key]
  have : (2 * m) • ((1 : ℝ) • (h (clampI ((2 * m)⁻¹ • x)) : W) + (1 / 2 : ℝ) • (h 1 : W))
      - m • (h 1 : W) = (2 * m) • (h (clampI ((2 * m)⁻¹ • x)) : W) := by
    match_scalars <;> ring
  rw [this]
  exact ou_smul_nonneg (by positivity) (h _).2.1

theorem extLin_unit (hh : IsAffineIvl h) : extLin hh (ouUnit V) = (h 1 : W) := by
  rw [extLin_apply]; exact extF_ivl hh 1

/-- A positive linear map is determined by its values on `[0,u]`. -/
theorem linear_ext_ivl {f g : V →ₗ[ℝ] W} (hfg : ∀ a : V, 0 ≤ a → a ≤ ouUnit V → f a = g a)
    (x : V) : f x = g x := by
  obtain ⟨n, hn⟩ := exists_validScale x
  set m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by positivity
  obtain ⟨a0, a1⟩ := validScale_mem hm hn
  have hx : x = (2 * m) • ((2 * m)⁻¹ • (x + m • ouUnit V)) - m • ouUnit V := by
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
  have e : ∀ φ : V →ₗ[ℝ] W, φ x = (2 * m) • φ ((2 * m)⁻¹ • (x + m • ouUnit V))
      - m • φ (ouUnit V) := by
    intro φ; conv_lhs => rw [hx]
    rw [map_sub, LinearMap.map_smul φ (2 * m), LinearMap.map_smul φ m]
  rw [e f, e g, hfg _ a0 a1, hfg _ ou_unit_nonneg le_rfl]

end Extension

/-! ## SIG 51: ordered vector spaces with an order unit, `OVSu` -/

/-- **SIG 51** (main.tex:1479, Definition): an **order unit** of an ordered
vector space `A` is a positive `u` such that every `x` has `-n u ≤ x ≤ n u`
for some `n ∈ ℕ`. -/
def IsOrderUnitPrinted {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] (e : A) :
    Prop :=
  0 ≤ e ∧ ∀ x : A, ∃ n : ℕ, -((n : ℝ) • e) ≤ x ∧ x ≤ (n : ℝ) • e

/-- **SIG 51** (main.tex:1479, Definition): the distinguished unit of the
tree's `OrderUnitSpace` (a translation-invariant order whose positive cone is
closed under non-negative scalars, with a unit dominating every element) is an
order unit in the printed sense; so an `OrderUnitSpace` is exactly an ordered
vector space with an order unit (the converse is `Papers.OAP.oap58_ofPaper`). -/
theorem ouUnit_isOrderUnitPrinted (A : Type u) [AddCommGroup A] [Module ℝ A] [PartialOrder A]
    [OrderUnitSpace A] : IsOrderUnitPrinted (ouUnit A) :=
  ⟨ou_unit_nonneg, Papers.OAP.oap58_orderUnit⟩

/-- **SIG 51** (main.tex:1479, Definition): an object of `OVSu`: an ordered
vector space with an order unit (the tree's `OrderUnitSpace`, which does not
ask for the Archimedean property). -/
structure OVSu : Type (u + 1) where
  carrier : Type u
  [grp : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [ord : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]

attribute [instance] OVSu.grp OVSu.mod OVSu.ord OVSu.ous

namespace OVSu

instance : CoeSort OVSu.{u} (Type u) := ⟨OVSu.carrier⟩

/-- **SIG 51** (main.tex:1486, Definition): a morphism of `OVSu`: a
**subunital** (`f u ≤ u`) **positive** (`f(A₊) ⊆ B₊`) linear map. -/
@[ext]
structure Hom (A B : OVSu.{u}) : Type u where
  toLin : A.carrier →ₗ[ℝ] B.carrier
  pos : ∀ x, 0 ≤ x → 0 ≤ toLin x
  subunital : toLin (ouUnit A.carrier) ≤ ouUnit B.carrier

theorem Hom.mono {A B : OVSu.{u}} (f : Hom A B) {x y : A.carrier} (h : x ≤ y) :
    f.toLin x ≤ f.toLin y := by
  have := f.pos (y - x) (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at this

/-- **SIG 51** (main.tex:1486, Definition): the category `OVSu`. -/
instance : Category OVSu.{u} where
  Hom := Hom
  id A := ⟨LinearMap.id, fun _ h => h, le_rfl⟩
  comp f g := ⟨g.toLin ∘ₗ f.toLin, fun x h => g.pos _ (f.pos x h),
    (g.mono f.subunital).trans g.subunital⟩

@[simp] theorem id_toLin (A : OVSu.{u}) : (𝟙 A : Hom A A).toLin = LinearMap.id := rfl
@[simp] theorem comp_toLin {A B C : OVSu.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toLin = g.toLin ∘ₗ f.toLin := rfl

theorem hom_ext {A B : OVSu.{u}} {f g : A ⟶ B} (h : ∀ x, f.toLin x = g.toLin x) : f = g :=
  Hom.ext (LinearMap.ext h)

end OVSu

/-! ## `EMod[M]`: effect modules and subunital maps -/

/-- **SIG 24** (main.tex:771, Definition), the finite case: an object of
`EMod[M]`, an effect `M`-module (the tree's `EffectModule`). -/
structure EModS (M : Type u) [EffectMonoid M] : Type (u + 1) where
  carrier : Type u
  [ea : EffectAlgebra carrier]
  [mod : EffectModule M carrier]

attribute [instance] EModS.ea EModS.mod

namespace EModS

variable {M : Type u} [EffectMonoid M]

instance : CoeSort (EModS M) (Type u) := ⟨EModS.carrier⟩

/-- **SIG 24** (main.tex:790, Definition): a morphism of `EMod[M]`: an
additive map preserving the action (not required to preserve `1`). -/
@[ext]
structure Hom (E F : EModS M) : Type u where
  toFun : E.carrier → F.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : M) (a : E.carrier), toFun (r • a) = r • toFun a

/-- **SIG 24** (main.tex:790, Definition): the category `EMod[M]`. -/
instance : Category (EModS M) where
  Hom := Hom
  id E := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun r a => by simp [f.map_smul, g.map_smul]⟩

@[simp] theorem id_toFun (E : EModS M) : (𝟙 E : Hom E E).toFun = id := rfl
@[simp] theorem comp_toFun {E F G : EModS M} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {E F : EModS M} {f g : E ⟶ F} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

/-- An additive, action-preserving bijection that reflects orthogonality is
an isomorphism of `EMod[M]`. -/
def isoOfEquiv {E F : EModS M} (e : E.carrier ≃ F.carrier) (hadd : IsAdditive e)
    (hperp : ∀ a b, Perp (e a) (e b) → Perp a b) (hsm : ∀ (r : M) a, e (r • a) = r • e a) :
    E ≅ F where
  hom := ⟨e, hadd, hsm⟩
  inv := ⟨e.symm, ⟨by rw [Equiv.symm_apply_eq]; exact hadd.1.symm, fun {x y} h => by
      obtain ⟨a, rfl⟩ := e.surjective x
      obtain ⟨b, rfl⟩ := e.surjective y
      have hab := hperp a b h
      obtain ⟨h', e'⟩ := hadd.2 hab
      simp only [Equiv.symm_apply_apply]
      exact ⟨hab, ((Equiv.symm_apply_eq e).2 e').symm⟩⟩,
    fun r x => by
      obtain ⟨a, rfl⟩ := e.surjective x
      rw [Equiv.symm_apply_eq, hsm, Equiv.apply_symm_apply]⟩
  hom_inv_id := hom_ext fun a => e.symm_apply_apply a
  inv_hom_id := hom_ext fun a => e.apply_symm_apply a

end EModS

/-! ## SIG 52: `OVSu ≃ EMod[[0,1]]` -/

section SIG52

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- The unit interval `[0,u]_A` as an object of `EMod[[0,1]]`. -/
noncomputable abbrev ivlObj (A : OVSu.{0}) : EModS I := EModS.mk (Ivl A.carrier)

/-- The restriction of a morphism of `OVSu` to the unit intervals. -/
noncomputable def ivlMap {A B : OVSu.{0}} (f : A ⟶ B) : ivlObj A ⟶ ivlObj B where
  toFun x := ⟨f.toLin x.1, f.pos _ x.2.1, (f.mono x.2.2).trans f.subunital⟩
  additive := ⟨Subtype.ext (map_zero f.toLin), fun {x y} h => by
    refine ⟨?_, Subtype.ext (map_add f.toLin x.1 y.1).symm⟩
    show f.toLin x.1 + f.toLin y.1 ≤ ouUnit B.carrier
    rw [← map_add]
    exact (f.mono h).trans f.subunital⟩
  map_smul r x := Subtype.ext (map_smul f.toLin (r : ℝ) x.1)

@[simp] theorem ivlMap_apply {A B : OVSu.{0}} (f : A ⟶ B) (x : (ivlObj A).carrier) :
    ((ivlMap f).toFun x).1 = f.toLin x.1 := rfl

/-- **SIG 52** (main.tex:1506): the functor `OVSu → EMod[[0,1]]`,
`(A, u) ↦ [0,u]_A`. -/
noncomputable def ivlFunctor : OVSu.{0} ⥤ EModS I where
  obj := ivlObj
  map := ivlMap
  map_id _ := rfl
  map_comp _ _ := rfl

theorem ivlMap_isAffine {A B : OVSu.{0}} (g : ivlObj A ⟶ ivlObj B) :
    IsAffineIvl (V := A.carrier) (W := B.carrier) g.toFun :=
  isAffineIvl_of g.additive g.map_smul

/-- The extension of a morphism `[0,u]_A → [0,u]_B` to a morphism of `OVSu`. -/
noncomputable def ivlPreimage {A B : OVSu.{0}} (g : ivlObj A ⟶ ivlObj B) : A ⟶ B where
  toLin := extLin (ivlMap_isAffine g)
  pos _ hx := extLin_nonneg (ivlMap_isAffine g) hx
  subunital := by rw [extLin_unit]; exact (g.toFun 1).2.2

theorem ivlMap_ivlPreimage {A B : OVSu.{0}} (g : ivlObj A ⟶ ivlObj B) :
    ivlMap (ivlPreimage g) = g :=
  EModS.hom_ext fun a => Subtype.ext (extF_ivl (ivlMap_isAffine g) a)

instance ivlFunctor_full : ivlFunctor.Full :=
  ⟨fun g => ⟨ivlPreimage g, ivlMap_ivlPreimage g⟩⟩

instance ivlFunctor_faithful : ivlFunctor.Faithful :=
  ⟨fun {A B} f g h => OVSu.hom_ext fun x => linear_ext_ivl (fun a h0 h1 => by
    have := congrArg (fun k : ivlObj A ⟶ ivlObj B => ((k.toFun ⟨a, h0, h1⟩ : Ivl B.carrier) :
      B.carrier)) h
    exact this) x⟩

/-- The Gudder–Pulmannová space of an effect `[0,1]`-module, as an object of
`OVSu`. -/
noncomputable def gpObj (E : EModS I) : OVSu.{0} := OVSu.mk (GP.Vec E.carrier)

/-- `[0,u]_{GP(E)} ≅ E` in `EMod[[0,1]]`. -/
noncomputable def gpIso (E : EModS I) : ivlObj (gpObj E) ≅ E :=
  (EModS.isoOfEquiv (E := E) (F := ivlObj (gpObj E)) (Papers.OAP.gpEquiv E.carrier)
    ⟨Subtype.ext GP.gmap_zero, fun {a b} h =>
      ⟨Papers.OAP.gmap_perp_iff.1 h, Subtype.ext (GP.gmap_ovee h).symm⟩⟩
    (fun a b h => Papers.OAP.gmap_perp_iff.2 h)
    (fun r a => Subtype.ext (GP.gmap_smul r a))).symm

instance ivlFunctor_essSurj : ivlFunctor.EssSurj :=
  ⟨fun E => ⟨gpObj E, ⟨gpIso E⟩⟩⟩

/-- **SIG 52** (`prop:OVSu-equiv-EMod`, main.tex:1506, Proposition, cited
[JacobsMF2016, Theorem 14]): the functor `OVSu → EMod[[0,1]]`,
`(A, u) ↦ [0,u]_A`, is an equivalence of categories.  Our proof: faithful
since `x = 2m·(x + m u)/2m - m u` with `(x + m u)/2m ∈ [0,u]`; full by
extending an additive, `[0,1]`-homogeneous `g : [0,u]_A → [0,u]_B` to
`F x = 2m·g((x + m u)/2m) - m·g(u)` (independent of `m`, additive,
`[0,1]`-homogeneous, hence linear; positive and subunital); essentially
surjective by the Gudder–Pulmannová representation (the tree's `GP.Vec`,
179III.2, with OAP 62's reflection of `⊥`). -/
theorem sig52 : ivlFunctor.IsEquivalence := { }

end SIG52

/-! ## SIG 53: order-unit spaces, the order-unit norm, Banach order-unit spaces -/

section SIG53

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A]

/-- **SIG 53** (main.tex:1513, Definition): an ordered vector space with order
unit is an **order-unit space** when it is Archimedean: `n x ≤ u` for all
`n ∈ ℕ` implies `x ≤ 0` (the tree's `OUSArchimedean`, in the printed form by
`ousArchimedean_iff_nsmul`). -/
theorem sig53_archimedean_iff :
    OUSArchimedean A ↔ ∀ x : A, (∀ n : ℕ, (n : ℝ) • x ≤ ouUnit A) → x ≤ 0 :=
  ousArchimedean_iff_nsmul

variable (A) in
/-- **SIG 53** (main.tex:1520, Definition): the **order-unit norm**
`‖a‖ = inf {r > 0 | -r u ≤ a ≤ r u}`. -/
noncomputable def ouNorm (a : A) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ -(r • ouUnit A) ≤ a ∧ a ≤ r • ouUnit A}

theorem ouNorm_le {a : A} {r : ℝ} (hr : 0 < r) (h1 : -(r • ouUnit A) ≤ a)
    (h2 : a ≤ r • ouUnit A) : ouNorm A a ≤ r :=
  csInf_le ⟨0, fun _ hs => hs.1.le⟩ ⟨hr, h1, h2⟩

theorem le_of_ouNorm_lt {a : A} {ε : ℝ} (h : ouNorm A a < ε) :
    -(ε • ouUnit A) ≤ a ∧ a ≤ ε • ouUnit A := by
  have hne : {r : ℝ | 0 < r ∧ -(r • ouUnit A) ≤ a ∧ a ≤ r • ouUnit A}.Nonempty := by
    obtain ⟨n, h1, h2⟩ := Papers.OAP.oap58_orderUnit a
    exact ⟨(n : ℝ) + 1, by positivity, (ValidScale.mono (m := (n : ℝ)) ⟨h1, h2⟩ (by linarith)).1,
      (ValidScale.mono (m := (n : ℝ)) ⟨h1, h2⟩ (by linarith)).2⟩
  obtain ⟨r, ⟨hr, h1, h2⟩, hrε⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨le_trans (neg_le_neg (ou_smul_unit_mono hrε.le)) h1, h2.trans (ou_smul_unit_mono hrε.le)⟩

variable (A) in
/-- **SIG 53** (main.tex:1524, Definition): a **Banach order-unit space**: an
order-unit space (Archimedean) complete for the order-unit norm (every
norm-Cauchy sequence converges). -/
def IsBanachOUS : Prop :=
  OUSArchimedean A ∧ ∀ s : ℕ → A,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ouNorm A (s m - s n) < ε) →
    ∃ v : A, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ouNorm A (s n - v) < ε

/-- Norm-completeness in the order form of `Papers.OAP.OUSNormComplete` gives
completeness for the order-unit norm. -/
theorem isBanachOUS_of (hA : OUSArchimedean A) (hC : Papers.OAP.OUSNormComplete A) :
    IsBanachOUS A := by
  refine ⟨hA, fun s hs => ?_⟩
  obtain ⟨v, hv⟩ := hC s fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    exact ⟨N, fun m hm n hn => (le_of_ouNorm_lt (hN m hm n hn)).2⟩
  refine ⟨v, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hv (ε / 2) (by positivity)
  refine ⟨N, fun n hn => lt_of_le_of_lt (ouNorm_le (by positivity) ?_ (hN n hn).1)
    (by linarith)⟩
  rw [neg_le, neg_sub]; exact (hN n hn).2

end SIG53

/-! ## SIG 54: monotone σ-completeness and σ-normal maps -/

section SIG54

variable (A : Type u) [AddCommGroup A] [Module ℝ A] [PartialOrder A]

/-- **SIG 54** (main.tex:1531, Definition): an ordered vector space is
**monotone σ-complete** if every ascending sequence bounded above has a
supremum. -/
def MonotoneSigmaComplete : Prop :=
  ∀ a : ℕ → A, Monotone a → BddAbove (Set.range a) → ∃ s, IsLUB (Set.range a) s

variable {A} {B : Type u} [AddCommGroup B] [Module ℝ B] [PartialOrder B]

/-- **SIG 54** (main.tex:1537, Definition): a map is **σ-normal** if it
preserves suprema of ascending sequences that are bounded above. -/
def SigmaNormal (f : A → B) : Prop :=
  ∀ a : ℕ → A, Monotone a → BddAbove (Set.range a) → ∀ s, IsLUB (Set.range a) s →
    IsLUB (Set.range fun n => f (a n)) (f s)

end SIG54

/-! ## SIG 68: halving commutes with suprema -/

section SIG68

variable {E : Type u} [EffectAlgebra E] [EffectModule I E]

open Papers.OAP (ihalf ihalf_perp ihalf_ovee)

theorem half_ovee_half (x : E) :
    ∃ h : Perp (ihalf • x) (ihalf • x), ovee (ihalf • x) (ihalf • x) h = x := by
  obtain ⟨h, e⟩ := EffectModule.perp_smul (E := E) ihalf_perp x
  exact ⟨h, by rw [e, ihalf_ovee, EffectModule.one_smul]⟩

theorem sig68_half (hE : OmegaComplete E) {a : ℕ → E} (ha : ∀ n, a n ≼ a (n + 1)) {s : E}
    (hs : IsSupOf (Set.range a) s) :
    IsSupOf (Set.range fun n => ihalf • a n) (ihalf • s) := by
  have hb : ∀ n, ihalf • a n ≼ ihalf • a (n + 1) := fun n => GP.smul_mono' (ha n) _
  obtain ⟨t, ht⟩ := hE _ hb
  have ht1 : t ≼ ihalf • (1 : E) :=
    ht.2 _ (by rintro _ ⟨n, rfl⟩; exact GP.smul_mono' (GP.ea_le_one _) _)
  obtain ⟨hp1, -⟩ := half_ovee_half (1 : E)
  have htt : Perp t t := GP.perp_of_le' ht1 ht1 hp1
  have hsup : IsSupOf (Set.range a) (ovee t t htt) := by
    constructor
    · rintro _ ⟨n, rfl⟩
      obtain ⟨hpn, en⟩ := half_ovee_half (a n)
      obtain ⟨_, le⟩ := ovee_le_ovee (ht.1 _ ⟨n, rfl⟩) (ht.1 _ ⟨n, rfl⟩) htt
      rwa [en] at le
    · intro c hc
      have htc : t ≼ ihalf • c :=
        ht.2 _ (by rintro _ ⟨n, rfl⟩; exact GP.smul_mono' (hc _ ⟨n, rfl⟩) _)
      obtain ⟨hpc, ec⟩ := half_ovee_half c
      obtain ⟨_, le⟩ := ovee_le_ovee htc htc hpc
      rwa [ec] at le
  have hst : s = ovee t t htt := hs.unique hsup
  have : ihalf • s = t := by
    rw [hst]
    obtain ⟨h', e⟩ := EffectModule.smul_perp ihalf htt
    obtain ⟨_, e'⟩ := half_ovee_half t
    rw [← e]; exact e'
  rw [this]; exact ht

/-- `2^{-N}` as a scalar in `[0,1]`. -/
noncomputable def ipow (N : ℕ) : I := GP.Iv ((1 / 2 : ℝ) ^ N)

theorem ipow_coe (N : ℕ) : ((ipow N : I) : ℝ) = (1 / 2 : ℝ) ^ N :=
  GP.Iv_coe (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem ipow_succ (N : ℕ) : ipow (N + 1) = ihalf * ipow N := by
  apply Subtype.ext
  rw [GP.I_coe_mul, ipow_coe, ipow_coe, pow_succ, mul_comm]; rfl

/-- **SIG 68** (`lem:emod-bigvee-commute`, main.tex:3036, Lemma): in an
ω-complete effect `[0,1]`-module, `⋁ₙ 2^{-N} aₙ = 2^{-N} ⋁ₙ aₙ` for every
ascending `(aₙ)`.  Proof as printed: `N = 1` shows `(⋁ ½aₙ) ⊕ (⋁ ½aₙ)` is
the supremum of the `aₙ`; induction on `N`. -/
theorem sig68 (hE : OmegaComplete E) {a : ℕ → E} (ha : ∀ n, a n ≼ a (n + 1)) {s : E}
    (hs : IsSupOf (Set.range a) s) (N : ℕ) :
    IsSupOf (Set.range fun n => ipow N • a n) (ipow N • s) := by
  induction N with
  | zero =>
    have h1 : ipow 0 = 1 := Subtype.ext (by rw [ipow_coe, pow_zero]; rfl)
    simp only [h1, EffectModule.one_smul]
    exact hs
  | succ N ih =>
    simp only [ipow_succ, EffectModule.mul_smul]
    exact sig68_half hE (fun n => GP.smul_mono' (ha n) _) ih

end SIG68

/-! ## SIG 69: monotone σ-completeness is ω-completeness of `[0,u]` -/

section SIG69

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A]

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

theorem exists_le_two_pow_smul (b : A) : ∃ M : ℕ, b ≤ ((2 : ℝ) ^ M) • ouUnit A := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit b
  refine ⟨n, hn.trans (ou_smul_unit_mono ?_)⟩
  exact_mod_cast (Nat.lt_two_pow_self).le

theorem two_pow_mul_half_pow (M : ℕ) : (2 : ℝ) ^ M * (1 / 2) ^ M = 1 := by
  rw [← mul_pow]; norm_num

/-- A supremum in `[0,u]` of an ascending sequence is its supremum in `A`
(when `[0,u]` is ω-complete): the argument of SIG 69's proof, with `N = 0`,
using SIG 68. -/
theorem isLUB_of_isSupOf_ivl (hE : OmegaComplete (Ivl A)) {c : ℕ → Ivl A}
    (hc : ∀ n, c n ≼ c (n + 1)) {t : Ivl A} (ht : IsSupOf (Set.range c) t) :
    IsLUB (Set.range fun n => (c n : A)) (t : A) := by
  refine ⟨by rintro _ ⟨n, rfl⟩; exact ivl_le_iff.1 (ht.1 _ ⟨n, rfl⟩), fun b hb => ?_⟩
  have hb0 : 0 ≤ b := (c 0).2.1.trans (hb ⟨0, rfl⟩)
  obtain ⟨M, hM⟩ := exists_le_two_pow_smul b
  have hq : (0 : ℝ) ≤ (1 / 2) ^ M := by positivity
  have d0 : 0 ≤ ((1 / 2 : ℝ) ^ M) • b := ou_smul_nonneg hq hb0
  have d1 : ((1 / 2 : ℝ) ^ M) • b ≤ ouUnit A := by
    have := ou_smul_le_smul hq hM
    rwa [smul_smul, mul_comm, two_pow_mul_half_pow, one_smul] at this
  have key := (sig68 hE hc ht M).2 (clampI (((1 / 2 : ℝ) ^ M) • b)) (by
    rintro _ ⟨n, rfl⟩
    rw [ivl_le_iff, ivl_smul_coe, clampI_coe d0 d1, ipow_coe]
    exact ou_smul_le_smul hq (hb ⟨n, rfl⟩))
  rw [ivl_le_iff, ivl_smul_coe, clampI_coe d0 d1, ipow_coe] at key
  have := ou_smul_le_smul (show (0 : ℝ) ≤ 2 ^ M by positivity) key
  rwa [smul_smul, smul_smul, two_pow_mul_half_pow, one_smul, one_smul] at this

/-- **SIG 69** (`lem:monotone-sigma-complete-iff-omega-complete`, main.tex:3072,
Lemma): an ordered vector space with order unit is monotone σ-complete iff its
unit interval `[0,u]` is ω-complete.  Proof as printed: translate an
ascending bounded sequence to start at `0`, scale it into `[0,u]` by `2^{-N}`,
and use SIG 68 to see that the supremum in `[0,u]`, scaled back, is the
supremum in `A` (`isLUB_of_isSupOf_ivl`). -/
theorem sig69 : MonotoneSigmaComplete A ↔ OmegaComplete (Ivl A) := by
  constructor
  · intro hA c hc
    have hmono : Monotone fun n => (c n : A) :=
      monotone_nat_of_le_succ fun n => ivl_le_iff.1 (hc n)
    obtain ⟨s, hs⟩ := hA _ hmono ⟨ouUnit A, by rintro _ ⟨n, rfl⟩; exact (c n).2.2⟩
    have hs0 : 0 ≤ s := (c 0).2.1.trans (hs.1 ⟨0, rfl⟩)
    have hs1 : s ≤ ouUnit A := hs.2 (by rintro _ ⟨n, rfl⟩; exact (c n).2.2)
    refine ⟨⟨s, hs0, hs1⟩, by rintro _ ⟨n, rfl⟩; exact ivl_le_iff.2 (hs.1 ⟨n, rfl⟩),
      fun d hd => ivl_le_iff.2 (hs.2 ?_)⟩
    rintro _ ⟨n, rfl⟩; exact ivl_le_iff.1 (hd _ ⟨n, rfl⟩)
  · intro hE a ha ⟨b, hb⟩
    obtain ⟨N, hN⟩ := exists_le_two_pow_smul (b - a 0)
    have hq : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    have mem : ∀ n, 0 ≤ ((1 / 2 : ℝ) ^ N) • (a n - a 0) ∧
        ((1 / 2 : ℝ) ^ N) • (a n - a 0) ≤ ouUnit A := fun n => by
      refine ⟨ou_smul_nonneg hq (sub_nonneg.2 (ha (Nat.zero_le n))), ?_⟩
      have h1 : a n - a 0 ≤ ((2 : ℝ) ^ N) • ouUnit A :=
        (sub_le_sub_right (hb ⟨n, rfl⟩) _).trans hN
      have := ou_smul_le_smul hq h1
      rwa [smul_smul, mul_comm, two_pow_mul_half_pow, one_smul] at this
    let c : ℕ → Ivl A := fun n => clampI (((1 / 2 : ℝ) ^ N) • (a n - a 0))
    have hcv : ∀ n, (c n : A) = ((1 / 2 : ℝ) ^ N) • (a n - a 0) := fun n =>
      clampI_coe (mem n).1 (mem n).2
    have hc : ∀ n, c n ≼ c (n + 1) := fun n => by
      rw [ivl_le_iff, hcv, hcv]
      exact ou_smul_le_smul hq (sub_le_sub_right (ha (Nat.le_succ n)) _)
    obtain ⟨t, ht⟩ := hE c hc
    have hl := isLUB_of_isSupOf_ivl hE hc ht
    have hinv : ∀ x : A, ((2 : ℝ) ^ N) • (((1 / 2 : ℝ) ^ N) • x) = x := fun x => by
      rw [smul_smul, two_pow_mul_half_pow, one_smul]
    refine ⟨a 0 + ((2 : ℝ) ^ N) • (t : A), ?_, fun b' hb' => ?_⟩
    · rintro _ ⟨n, rfl⟩
      have := ou_smul_le_smul (show (0 : ℝ) ≤ 2 ^ N by positivity) (hl.1 ⟨n, rfl⟩)
      simp only [hcv, hinv] at this
      exact sub_le_iff_le_add'.1 this
    · have := hl.2 (show ((1 / 2 : ℝ) ^ N) • (b' - a 0) ∈ upperBounds _ by
        rintro _ ⟨n, rfl⟩
        simp only [hcv]
        exact ou_smul_le_smul hq (sub_le_sub_right (hb' ⟨n, rfl⟩) _))
      have := ou_smul_le_smul (show (0 : ℝ) ≤ 2 ^ N by positivity) this
      rw [hinv] at this
      exact le_sub_iff_add_le'.1 this

end SIG69

/-! ## SIG 70: σ-normality is ω-continuity on `[0,u]` -/

section SIG70

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A]
variable {B : Type u} [AddCommGroup B] [Module ℝ B] [PartialOrder B] [OrderUnitSpace B]

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- The affine order automorphism `x ↦ q (x - c)` (`q > 0`). -/
noncomputable def affOI (q : ℝ) (hq : 0 < q) (c : A) : A ≃o A where
  toFun x := q • (x - c)
  invFun y := q⁻¹ • y + c
  left_inv x := by
    simp only [smul_smul, inv_mul_cancel₀ hq.ne', one_smul, sub_add_cancel]
  right_inv y := by
    simp only [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  map_rel_iff' := by
    intro x y
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have := ou_smul_le_smul (inv_nonneg.2 hq.le) h
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hq.ne', one_smul, one_smul] at this
      exact sub_le_sub_iff_right c |>.1 this
    · intro h; exact ou_smul_le_smul hq.le (sub_le_sub_right h c)

theorem isLUB_affine_iff (q : ℝ) (hq : 0 < q) (c : A) (a : ℕ → A) (s : A) :
    IsLUB (Set.range fun n => q • (a n - c)) (q • (s - c)) ↔ IsLUB (Set.range a) s := by
  have e : (Set.range fun n => q • (a n - c)) = affOI q hq c '' Set.range a := by
    rw [← Set.range_comp]; rfl
  rw [e]
  exact (affOI q hq c).isLUB_image'

/-- The restriction `[0,u]_A → [0,u]_B` of a positive subunital linear map. -/
def ivlRes (f : A →ₗ[ℝ] B) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hsub : f (ouUnit A) ≤ ouUnit B) (x : Ivl A) : Ivl B :=
  ⟨f x.1, hpos _ x.2.1, by
    have := hpos _ (sub_nonneg.2 x.2.2)
    rw [map_sub, sub_nonneg] at this
    exact this.trans hsub⟩

theorem mono_of_pos {f : A →ₗ[ℝ] B} (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) {x y : A} (h : x ≤ y) :
    f x ≤ f y := by
  have := hpos _ (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at this

/-- **SIG 70** (`lem:monotone-sigma-complete-iff-omega-complete-morphism`,
main.tex:3123, Lemma): a subunital positive linear map between monotone
σ-complete ordered vector spaces with order unit is σ-normal iff its
restriction `[0,u]_A → [0,u]_B` is ω-continuous.  Printed without proof
("by translation and scaling"); ours follows the hidden Auxproof: suprema of
chains in `[0,u]` are suprema in the space (SIG 69), and translation and
scaling preserve suprema. -/
theorem sig70 (hA : MonotoneSigmaComplete A) (hB : MonotoneSigmaComplete B) (f : A →ₗ[ℝ] B)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hsub : f (ouUnit A) ≤ ouUnit B) :
    SigmaNormal f ↔ IsOmegaContinuous (ivlRes f hpos hsub) := by
  have hA' := sig69.1 hA
  have hB' := sig69.1 hB
  constructor
  · intro hf c hc t ht
    have hl := isLUB_of_isSupOf_ivl hA' hc ht
    have hmono : Monotone fun n => (c n : A) :=
      monotone_nat_of_le_succ fun n => ivl_le_iff.1 (hc n)
    have hfl := hf _ hmono ⟨ouUnit A, by rintro _ ⟨n, rfl⟩; exact (c n).2.2⟩ _ hl
    refine ⟨by rintro _ ⟨n, rfl⟩; exact ivl_le_iff.2 (hfl.1 ⟨n, rfl⟩), fun d hd => ?_⟩
    refine ivl_le_iff.2 (hfl.2 ?_)
    rintro _ ⟨n, rfl⟩; exact ivl_le_iff.1 (hd _ ⟨n, rfl⟩)
  · intro hf a ha ⟨b, hb⟩ s hs
    obtain ⟨N, hN⟩ := exists_le_two_pow_smul (b - a 0)
    set q : ℝ := (1 / 2) ^ N
    have hq : 0 < q := by positivity
    have hsb : s ≤ b := hs.2 hb
    have hs0 : a 0 ≤ s := hs.1 ⟨0, rfl⟩
    have memx : ∀ x, a 0 ≤ x → x ≤ b → 0 ≤ q • (x - a 0) ∧ q • (x - a 0) ≤ ouUnit A := by
      intro x h0 h1
      refine ⟨ou_smul_nonneg hq.le (sub_nonneg.2 h0), ?_⟩
      have := ou_smul_le_smul hq.le ((sub_le_sub_right h1 _).trans hN)
      rwa [smul_smul, mul_comm, two_pow_mul_half_pow, one_smul] at this
    have mem : ∀ n, 0 ≤ q • (a n - a 0) ∧ q • (a n - a 0) ≤ ouUnit A := fun n =>
      memx _ (ha (Nat.zero_le n)) (hb ⟨n, rfl⟩)
    let c : ℕ → Ivl A := fun n => clampI (q • (a n - a 0))
    have hcv : ∀ n, (c n : A) = q • (a n - a 0) := fun n => clampI_coe (mem n).1 (mem n).2
    have hc : ∀ n, c n ≼ c (n + 1) := fun n => by
      rw [ivl_le_iff, hcv, hcv]
      exact ou_smul_le_smul hq.le (sub_le_sub_right (ha (Nat.le_succ n)) _)
    obtain ⟨t0, t1⟩ := memx s hs0 hsb
    let t : Ivl A := clampI (q • (s - a 0))
    have htv : (t : A) = q • (s - a 0) := clampI_coe t0 t1
    have hlA : IsLUB (Set.range fun n => (c n : A)) (t : A) := by
      simp only [hcv, htv]; exact (isLUB_affine_iff q hq (a 0) a s).2 hs
    have ht : IsSupOf (Set.range c) t := by
      refine ⟨by rintro _ ⟨n, rfl⟩; exact ivl_le_iff.2 (hlA.1 ⟨n, rfl⟩), fun d hd => ?_⟩
      refine ivl_le_iff.2 (hlA.2 ?_)
      rintro _ ⟨n, rfl⟩; exact ivl_le_iff.1 (hd _ ⟨n, rfl⟩)
    have hrc : ∀ n, ivlRes f hpos hsub (c n) ≼ ivlRes f hpos hsub (c (n + 1)) := fun n =>
      ivl_le_iff.2 (mono_of_pos hpos (ivl_le_iff.1 (hc n)))
    have h1 := isLUB_of_isSupOf_ivl hB' hrc (hf c hc t ht)
    have e1 : ∀ n, ((ivlRes f hpos hsub (c n) : Ivl B) : B) = q • (f (a n) - f (a 0)) :=
      fun n => by
        show f (c n : A) = _
        rw [hcv, map_smul, map_sub]
    have e2 : ((ivlRes f hpos hsub t : Ivl B) : B) = q • (f s - f (a 0)) := by
      show f (t : A) = _
      rw [htv, map_smul, map_sub]
    simp only [e1, e2] at h1
    exact (isLUB_affine_iff q hq (f (a 0)) (fun n => f (a n)) (f s)).1 h1

end SIG70

/-! ## SIG 71: Wright's lemma -/

/-- **SIG 71** (`lem:monotone-sigma-complete-bous`, main.tex:3162, Lemma,
cited [Wright 1972, Lemmas 1.1–1.2]): every monotone σ-complete ordered vector
space with order unit is a Banach order-unit space.  Not proved in the paper;
ours is OAP's: Archimedean by `Papers.OAP.oap61`, norm-complete by
`Papers.OAP.wright_normComplete` (Wright's argument). -/
theorem sig71 {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A]
    (hA : MonotoneSigmaComplete A) : IsBanachOUS A :=
  isBanachOUS_of (Papers.OAP.oap61 hA) (Papers.OAP.wright_normComplete hA)

/-! ## SIG 72: ω-complete convex effect algebras are σ-effect modules -/

section SIG72

variable {E : Type u} [EffectAlgebra E]

/-- ω-completeness in SIG's sense (SIG 17) is OAP's (OAP 13). -/
theorem omegaComplete_iff_oap : OmegaComplete E ↔ Papers.OAP.OmegaComplete E := by
  constructor
  · intro h
    exact ⟨fun f hf => by
      obtain ⟨s, hs⟩ := h f fun n => hf (Nat.le_succ n)
      exact ⟨s, hs.1, fun c hc => hs.2 c hc⟩⟩
  · intro h a ha
    let _ := Papers.OAP.eaPartialOrder E
    obtain ⟨s, hs⟩ := h.exists_isLUB a (monotone_nat_of_le_succ ha)
    exact ⟨s, hs.1, fun c hc => hs.2 hc⟩

variable [EffectModule I E]

theorem smul_le_smul_scalar {l m : I} (h : l ≼ m) (a : E) : l • a ≼ m • a := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨h', e⟩ := EffectModule.perp_smul hd a
  exact ⟨d • a, h', e⟩

theorem gmap_le_iff {a b : E} : GP.gmap a ≤ GP.gmap b ↔ a ≼ b :=
  Papers.OAP.gmap_le_gmap_iff

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- **SIG 72** (`lem:omega-complete-emod-is-sigma-emod`, main.tex:3170,
Lemma): every ω-complete effect `[0,1]`-module is a σ-effect
`[0,1]`-module.  Proof as printed: by SIG 20 it suffices that the action is
ω-continuous in each argument; represent `E` as `[0,u]_V` (SIG 52; here the
Gudder–Pulmannová space `V = GP.Vec E`, Archimedean by SIG 69/71); continuity
in the scalar by the Archimedean property, continuity in the vector because
`r · (-)` is an order isomorphism of `V` for `r > 0` and suprema in `[0,u]`
are suprema in `V`. -/
theorem sig72 (hE : OmegaComplete E) : IsSigmaEffectModule I E := by
  have := omegaComplete_iff_oap.1 hE
  have hArch : OUSArchimedean (GP.Vec E) := Papers.OAP.gp_archimedean
  have hIvl : OmegaComplete (Ivl (GP.Vec E)) :=
    omegaComplete_iff_oap.2 Papers.OAP.gp_omegaComplete
  -- continuity in the scalar
  have hscal : ∀ a : E, IsOmegaContinuous (fun r : I => r • a) := by
    intro a r hr ρ hρ
    refine ⟨by rintro _ ⟨n, rfl⟩; exact smul_le_smul_scalar (hρ.1 _ ⟨n, rfl⟩) a,
      fun b hb => ?_⟩
    rw [← gmap_le_iff]
    rw [← sub_nonpos]
    refine hArch _ fun ε hε => ?_
    obtain ⟨m, hm⟩ : ∃ m, (ρ : ℝ) < r m + ε := by
      by_contra hcon
      push Not at hcon
      have h0 : 0 ≤ (ρ : ℝ) - ε := by linarith [(r 0).2.1, hcon 0]
      have h1 : (ρ : ℝ) - ε ≤ 1 := by linarith [ρ.2.2]
      have := hρ.2 (GP.Iv ((ρ : ℝ) - ε)) (by
        rintro _ ⟨n, rfl⟩
        rw [unitInterval_le_iff, GP.Iv_coe h0 h1]; linarith [hcon n])
      rw [unitInterval_le_iff, GP.Iv_coe h0 h1] at this
      linarith
    have hrm : (r m : ℝ) ≤ ρ := unitInterval_le_iff.1 (hρ.1 _ ⟨m, rfl⟩)
    have hga := GP.gmap_nonneg a
    have hgu := GP.gmap_le_gunit a
    have hb' : GP.gmap (r m • a) ≤ GP.gmap b := gmap_le_iff.2 (hb _ ⟨m, rfl⟩)
    rw [GP.gmap_smul] at hb' ⊢
    have : (ρ : ℝ) • GP.gmap a = (r m : ℝ) • GP.gmap a + ((ρ : ℝ) - r m) • GP.gmap a := by
      rw [← add_smul]; congr 1; ring
    rw [this]
    have h2 : ((ρ : ℝ) - r m) • GP.gmap a ≤ ε • (GP.gunit : GP.Vec E) :=
      (ou_smul_le_smul (by linarith) hgu).trans (ou_smul_unit_mono (X := GP.Vec E) (by linarith))
    have := add_le_add hb' h2
    rw [sub_le_iff_le_add']
    exact this
  -- continuity in the vector
  have hvec : ∀ r : I, IsOmegaContinuous (fun a : E => r • a) := by
    intro r a ha s hs
    refine ⟨by rintro _ ⟨n, rfl⟩; exact GP.smul_mono' (hs.1 _ ⟨n, rfl⟩) r, fun b hb => ?_⟩
    by_cases hr : (r : ℝ) = 0
    · have : r = 0 := Subtype.ext hr
      show r • s ≼ b
      rw [this, GP.zero_smul']; exact GP.ea_zero_le b
    have hr0 : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 (Ne.symm hr)
    -- `gmap s` is the supremum of the `gmap aₙ` in `V`
    let c : ℕ → Ivl (GP.Vec E) := fun n => Papers.OAP.gpEquiv E (a n)
    have hc : ∀ n, c n ≼ c (n + 1) := fun n => ivl_le_iff.2 (gmap_le_iff.2 (ha n))
    have hsup : IsSupOf (Set.range c) (Papers.OAP.gpEquiv E s) := by
      refine ⟨by rintro _ ⟨n, rfl⟩; exact ivl_le_iff.2 (gmap_le_iff.2 (hs.1 _ ⟨n, rfl⟩)),
        fun d hd => ?_⟩
      obtain ⟨d', rfl⟩ := (Papers.OAP.gpEquiv E).surjective d
      refine ivl_le_iff.2 (gmap_le_iff.2 (hs.2 _ ?_))
      rintro _ ⟨n, rfl⟩
      exact gmap_le_iff.1 (ivl_le_iff.1 (hd _ ⟨n, rfl⟩))
    have hl := isLUB_of_isSupOf_ivl hIvl hc hsup
    have hub : (r : ℝ)⁻¹ • GP.gmap b ∈ upperBounds (Set.range fun n => (c n : GP.Vec E)) := by
      rintro _ ⟨n, rfl⟩
      have := gmap_le_iff.2 (hb _ ⟨n, rfl⟩)
      rw [GP.gmap_smul] at this
      have := ou_smul_le_smul (inv_nonneg.2 hr0.le) this
      rwa [smul_smul, inv_mul_cancel₀ hr0.ne', one_smul] at this
    have := ou_smul_le_smul hr0.le (hl.2 hub)
    rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul] at this
    rw [← gmap_le_iff, GP.gmap_smul]
    exact this
  have hbi := effectModule_biadditive (M := I) (E := E)
  exact ⟨hE, fun r => (sigmaAdditive_iff_omegaContinuous (hbi.1 r)).2 (hvec r),
    fun a => (sigmaAdditive_iff_omegaContinuous (hbi.2 a)).2 (hscal a)⟩

end SIG72

/-! ## SIG 54 (cont.): the category `sBOUS` -/

theorem SigmaNormal.comp {A B C : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A]
    [AddCommGroup B] [Module ℝ B] [PartialOrder B] [AddCommGroup C] [Module ℝ C]
    [PartialOrder C] {f : A → B} {g : B → C} (hfm : Monotone f) (hf : SigmaNormal f)
    (hg : SigmaNormal g) : SigmaNormal (g ∘ f) := by
  intro a ha hb s hs
  obtain ⟨b, hb⟩ := hb
  exact hg _ (hfm.comp ha) ⟨f b, by rintro _ ⟨n, rfl⟩; exact hfm (hb ⟨n, rfl⟩)⟩ _
    (hf a ha ⟨b, hb⟩ s hs)

/-- **SIG 54** (main.tex:1539, Definition): an object of `sBOUS`: a monotone
σ-complete Banach order-unit space. -/
structure SBOUS : Type 1 where
  toOVSu : OVSu.{0}
  msc : MonotoneSigmaComplete toOVSu.carrier
  banach : IsBanachOUS toOVSu.carrier

namespace SBOUS

/-- **SIG 54** (main.tex:1539, Definition): the category `sBOUS` of monotone
σ-complete Banach order-unit spaces and σ-normal subunital positive linear
maps. -/
instance : Category SBOUS where
  Hom A B := {f : A.toOVSu ⟶ B.toOVSu // SigmaNormal f.toLin}
  id A := ⟨𝟙 A.toOVSu, fun _ _ _ _ hs => by simpa using hs⟩
  comp f g := ⟨f.1 ≫ g.1, SigmaNormal.comp (f := f.1.toLin) (g := g.1.toLin)
    (fun _ _ h => f.1.mono h) f.2 g.2⟩

theorem hom_ext {A B : SBOUS} {f g : A ⟶ B} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp] theorem comp_val {A B C : SBOUS} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).1 = f.1 ≫ g.1 := rfl
@[simp] theorem id_val (A : SBOUS) : (𝟙 A : A ⟶ A).1 = 𝟙 A.toOVSu := rfl

end SBOUS

/-! ## SIG 55: `sBOUS ≃ sEMod[[0,1]]` -/

section SIG55

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- A mutually inverse pair of additive maps between effect algebras is
σ-additive (it is an order isomorphism, hence ω-continuous; SIG 20). -/
theorem isSigmaAdditiveC_of_inverse {X Y : Type u} [EffectAlgebra X] [EffectAlgebra Y]
    {f : X → Y} {g : Y → X} (hf : IsAdditive f) (hg : IsAdditive g) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) : IsSigmaAdditiveC f := by
  refine (sigmaAdditive_iff_omegaContinuous hf).2 fun a _ s hs => ?_
  refine ⟨by rintro _ ⟨n, rfl⟩; exact (additive_subunital f hf).2 _ _ (hs.1 _ ⟨n, rfl⟩),
    fun c hc => ?_⟩
  have : s ≼ g c := hs.2 _ (by
    rintro _ ⟨n, rfl⟩
    have := (additive_subunital g hg).2 _ _ (hc _ ⟨n, rfl⟩)
    rwa [hgf] at this)
  have := (additive_subunital f hf).2 _ _ this
  rwa [hfg] at this

theorem EModS.iso_hom_inv_apply {M : Type u} [EffectMonoid M] {E F : EModS M} (e : E ≅ F)
    (x : E.carrier) : e.inv.toFun (e.hom.toFun x) = x :=
  congrArg (fun k : E ⟶ E => k.toFun x) e.hom_inv_id

theorem EModS.iso_inv_hom_apply {M : Type u} [EffectMonoid M] {E F : EModS M} (e : E ≅ F)
    (y : F.carrier) : e.hom.toFun (e.inv.toFun y) = y :=
  congrArg (fun k : F ⟶ F => k.toFun y) e.inv_hom_id

/-- An isomorphism of the underlying effect modules is one of σ-effect
modules. -/
def SEMod.isoOfEMod {M : Type u} [EffectMonoid M] {X Y : SEMod M}
    (e : EModS.mk (M := M) X.carrier ≅ EModS.mk Y.carrier) : X ≅ Y where
  hom := ⟨e.hom.toFun, e.hom.additive, e.hom.map_smul,
    isSigmaAdditiveC_of_inverse e.hom.additive e.inv.additive
      (EModS.iso_hom_inv_apply e) (EModS.iso_inv_hom_apply e)⟩
  inv := ⟨e.inv.toFun, e.inv.additive, e.inv.map_smul,
    isSigmaAdditiveC_of_inverse e.inv.additive e.hom.additive
      (EModS.iso_inv_hom_apply e) (EModS.iso_hom_inv_apply e)⟩
  hom_inv_id := SEMod.hom_ext fun x => EModS.iso_hom_inv_apply e x
  inv_hom_id := SEMod.hom_ext fun y => EModS.iso_inv_hom_apply e y

/-- `[0,u]_A` of `A ∈ sBOUS`, as a σ-effect `[0,1]`-module (SIG 69, SIG 72). -/
noncomputable def sbousObj (A : SBOUS) : SEMod I :=
  SEMod.mk (Ivl A.toOVSu.carrier) (sig72 (sig69.1 A.msc))

/-- **SIG 55** (main.tex:1551): the functor `sBOUS → sEMod[[0,1]]`,
`A ↦ [0,u]_A` (the restriction of SIG 52's functor). -/
noncomputable def sbousFunctor : SBOUS ⥤ SEMod I where
  obj := sbousObj
  map {A B} f := ⟨(ivlMap f.1).toFun, (ivlMap f.1).additive, (ivlMap f.1).map_smul,
    (sigmaAdditive_iff_omegaContinuous (ivlMap f.1).additive).2
      ((sig70 A.msc B.msc f.1.toLin f.1.pos f.1.subunital).1 f.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance sbousFunctor_faithful : sbousFunctor.Faithful :=
  ⟨fun {A B} f g h => SBOUS.hom_ext (ivlFunctor.map_injective (EModS.hom_ext fun a =>
    congrArg (fun k : sbousObj A ⟶ sbousObj B => k.toFun a) h))⟩

instance sbousFunctor_full : sbousFunctor.Full := by
  refine ⟨fun {A B} g => ?_⟩
  let g' : ivlObj A.toOVSu ⟶ ivlObj B.toOVSu := ⟨g.toFun, g.additive, g.map_smul⟩
  have hres : ivlRes (ivlPreimage g').toLin (ivlPreimage g').pos (ivlPreimage g').subunital =
      g.toFun := funext fun a => Subtype.ext (extF_ivl (ivlMap_isAffine g') a)
  have hn : SigmaNormal (ivlPreimage g').toLin := by
    refine (sig70 A.msc B.msc _ (ivlPreimage g').pos (ivlPreimage g').subunital).2 ?_
    rw [hres]
    exact (sigmaAdditive_iff_omegaContinuous g.additive).1 g.sigma
  exact ⟨⟨ivlPreimage g', hn⟩, SEMod.hom_ext fun a => Subtype.ext
    (extF_ivl (ivlMap_isAffine g') a)⟩

/-- The object of `sBOUS` representing a σ-effect `[0,1]`-module: its
Gudder–Pulmannová space. -/
noncomputable def gpSBOUS (E : SEMod I) : SBOUS :=
  have : Papers.OAP.OmegaComplete E.carrier := omegaComplete_iff_oap.1 E.sigma.1
  have hmsc : MonotoneSigmaComplete (GP.Vec E.carrier) :=
    sig69.2 (omegaComplete_iff_oap.2 Papers.OAP.gp_omegaComplete)
  ⟨gpObj (EModS.mk E.carrier), hmsc, sig71 hmsc⟩

instance sbousFunctor_essSurj : sbousFunctor.EssSurj :=
  ⟨fun E => ⟨gpSBOUS E, ⟨SEMod.isoOfEMod (gpIso (EModS.mk E.carrier))⟩⟩⟩

/-- **SIG 55** (`prop:sBOUS-equiv-sEMod`, main.tex:1551, Proposition): there
is an equivalence of categories `sBOUS ≃ sEMod[[0,1]]`, `A ↦ [0,u]_A`.  Proof
as printed (App. C): SIG 52's equivalence restricts, by SIG 69 and SIG 70, to
monotone σ-complete spaces with σ-normal maps and ω-complete modules with
ω-continuous maps, which are `sBOUS` (SIG 71) and `sEMod[[0,1]]` (SIG 72, and
SIG 20 for the maps). -/
theorem sig55 : sbousFunctor.IsEquivalence := { }

end SIG55

/-! ## Transporting σ-effectus structure along a fully faithful functor -/

namespace SigmaPAM

variable {α : Type u} {β : Type v} [SigmaPAM β] (e : α ≃ β)

/-- The σ-PAM on `α` transported along a bijection `e : α ≃ β`. -/
noncomputable def ofEquiv : SigmaPAM α where
  Summable x := Summable (fun j => e (x j))
  sum x h := e.symm (sum (fun j => e (x j)) h)
  nonempty := ⟨e.symm (Classical.choice nonempty)⟩
  summable_iff_partition x p := by
    rw [summable_iff_partition (fun j => e (x j)) p]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, by simpa only [Equiv.apply_symm_apply] using h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, by simpa only [Equiv.apply_symm_apply] using h'⟩
  sum_partition x p hx h h' := by
    have h'' : Summable (fun k => sum (fun j : {j // p j = k} => e (x j.1)) (h k)) := by
      simpa only [Equiv.apply_symm_apply] using h'
    rw [SigmaPAM.sum_partition (fun j => e (x j)) p hx h h'']
    congr 1
    exact sum_congr (funext fun k => (e.apply_symm_apply _).symm) _ _
  summable_unique x := summable_unique _
  sum_unique x h := by
    show e.symm _ = _
    rw [SigmaPAM.sum_unique, Equiv.symm_apply_apply]
  limit x hF := limit _ hF

theorem ofEquiv_sumsTo_iff {J : Type} [Countable J] (x : J → α) (s : α) :
    @SumsTo α (ofEquiv e) J _ x s ↔ SumsTo (fun j => e (x j)) (e s) := by
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, by rw [← hs]; exact (e.apply_symm_apply _).symm⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, by show e.symm _ = s; rw [hs, e.symm_apply_apply]⟩

end SigmaPAM

section Transport

variable {D : Type u} [Category.{v} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasCountableCoproducts D']
  [∀ X Y : D', SigmaPAM (X ⟶ Y)]
variable (F : D' ⥤ D)

/-- `F` **reflects and preserves sums** of maps. -/
def SumsCompatible : Prop :=
  ∀ {X Y : D'} {J : Type} [Countable J] (x : J → (X ⟶ Y)) (s : X ⟶ Y),
    SumsTo x s ↔ SumsTo (fun j => F.map (x j)) (F.map s)

variable {F} [F.Full] [F.Faithful] (hsum : SumsCompatible F)
include hsum

theorem SumsCompatible.map_zero {X Y : D'} : F.map (0 : X ⟶ Y) = 0 := by
  have := (hsum (Empty.elim : Empty → (X ⟶ Y)) SigmaPAM.zero).1 (sumsTo_of_isEmpty _)
  exact this.unique (sumsTo_of_isEmpty _)

theorem SumsCompatible.pair_iff {X Y : D'} (f g s : X ⟶ Y) :
    SumsTo ![f, g] s ↔ SumsTo ![F.map f, F.map g] (F.map s) := by
  rw [hsum]
  exact sumsTo_congr (fun i => by fin_cases i <;> rfl)

theorem SumsCompatible.perp_iff {X Y : D'} (f g : X ⟶ Y) :
    Perp f g ↔ Perp (F.map f) (F.map g) := by
  constructor
  · intro h
    exact ((hsum.pair_iff f g _).1 (sumsTo_sum h)).summable
  · intro h
    obtain ⟨s, hs⟩ : ∃ s, SumsTo ![F.map f, F.map g] s := ⟨_, sumsTo_sum h⟩
    rw [← F.map_preimage s] at hs
    exact ((hsum.pair_iff f g _).2 hs).summable

theorem SumsCompatible.map_ovee {X Y : D'} {f g : X ⟶ Y} (h : Perp f g) :
    F.map (ovee f g h) = ovee (F.map f) (F.map g) ((hsum.perp_iff f g).1 h) :=
  (((hsum.pair_iff f g _).1 (sumsTo_sum h)).sum_eq _).symm

theorem SumsCompatible.summable_iff {X Y : D'} {J : Type} [Countable J] (x : J → (X ⟶ Y)) :
    Summable x ↔ Summable (fun j => F.map (x j)) := by
  constructor
  · intro h; exact ((hsum x _).1 (sumsTo_sum h)).summable
  · intro h
    obtain ⟨s, hs⟩ : ∃ s, SumsTo (fun j => F.map (x j)) s := ⟨_, sumsTo_sum h⟩
    rw [← F.map_preimage s] at hs
    exact ((hsum x _).2 hs).summable

/-- `F` maps the partial projections of `D'` to those of `D`, up to the
comparison isomorphism. -/
theorem SumsCompatible.map_pproj
    (hpres : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F)
    {J : Type} [Countable J] (X : J → D') (j : J) :
    have := hpres J
    F.map (pproj X j) = inv (sigmaComparison F X) ≫ pproj (fun k => F.obj (X k)) j := by
  have := hpres J
  rw [IsIso.eq_inv_comp]
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_comp_sigmaComparison, ← F.map_comp]
  by_cases hk : k = j
  · subst hk
    rw [ι_pproj_self, ι_pproj_self, F.map_id]
  · rw [ι_pproj_ne _ hk, ι_pproj_ne _ hk, hsum.map_zero]

/-- The σ-PAC structure of `D'` from that of `D`. -/
theorem SumsCompatible.sigmaPAC
    (hpres : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F) :
    SigmaPAC D' where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s h => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s h => ?_⟩
    · refine (hsum _ _).2 ?_
      simp only [F.map_comp]
      exact comp_sumsTo_left (F.map g) ((hsum x s).1 h)
    · refine (hsum _ _).2 ?_
      simp only [F.map_comp]
      exact comp_sumsTo_right (F.map f) ((hsum x s).1 h)
  compatible_sum {J} _ A B f hc := by
    obtain ⟨g, hg⟩ := hc
    have := hpres J
    refine (hsum.summable_iff f).2 (SigmaPAC.compatible_sum _ ⟨F.map g ≫
      inv (sigmaComparison F (fun _ : J => B)), fun j => ?_⟩)
    rw [Category.assoc, ← hsum.map_pproj hpres, ← F.map_comp, hg]
  untying {A B f g} h := by
    rw [hsum.summable_iff] at h ⊢
    have e1 : (fun j => F.map (![f, g] j)) = ![F.map f, F.map g] := by
      funext i; fin_cases i <;> rfl
    rw [e1] at h
    have h2 := SigmaPAC.untying h
    let ψ : F.obj B ⨿ F.obj B ⟶ F.obj (B ⨿ B) :=
      coprod.desc (F.map coprod.inl) (F.map coprod.inr)
    have h3 := comp_sumsTo_left ψ (sumsTo_sum h2)
    have e2 : (fun j => ![F.map f ≫ coprod.inl, F.map g ≫ coprod.inr] j ≫ ψ) =
        fun j => F.map (![f ≫ coprod.inl, g ≫ coprod.inr] j) := by
      funext i; fin_cases i
      · show (F.map f ≫ coprod.inl) ≫ ψ = F.map (f ≫ coprod.inl)
        rw [Category.assoc, coprod.inl_desc, F.map_comp]
      · show (F.map g ≫ coprod.inr) ≫ ψ = F.map (g ≫ coprod.inr)
        rw [Category.assoc, coprod.inr_desc, F.map_comp]
    rw [e2] at h3
    exact h3.summable

end Transport

section TransportEffectus

variable {D : Type u} [Category.{v} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasCountableCoproducts D']
  [∀ X Y : D', SigmaPAM (X ⟶ Y)]
variable {F : D' ⥤ D} [F.Full] [F.Faithful] (hsum : SumsCompatible F)
  (I' : D') (e : F.obj I' ≅ SigmaEffectus.«I» (C := D))
include hsum

theorem SumsCompatible.pred_sumsTo_iff {X : D'} {J : Type} [Countable J] (x : J → (X ⟶ I'))
    (s : X ⟶ I') :
    SumsTo x s ↔ SumsTo (fun j => F.map (x j) ≫ e.hom) (F.map s ≫ e.hom) := by
  rw [hsum]
  constructor
  · exact comp_sumsTo_left e.hom
  · intro h
    have := comp_sumsTo_left e.inv h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

theorem SumsCompatible.pred_perp_iff {X : D'} (p q : X ⟶ I') :
    Perp p q ↔ Perp (F.map p ≫ e.hom) (F.map q ≫ e.hom) := by
  have key : ∀ s, SumsTo ![p, q] s ↔
      SumsTo ![F.map p ≫ e.hom, F.map q ≫ e.hom] (F.map s ≫ e.hom) := fun s => by
    rw [hsum.pred_sumsTo_iff I' e]
    exact sumsTo_congr (fun i => by fin_cases i <;> rfl)
  constructor
  · intro h; exact ((key _).1 (sumsTo_sum h)).summable
  · intro h
    obtain ⟨s, hs⟩ : ∃ s, SumsTo ![F.map p ≫ e.hom, F.map q ≫ e.hom] s := ⟨_, sumsTo_sum h⟩
    rw [← Category.comp_id s, ← e.inv_hom_id, ← Category.assoc, ← F.map_preimage (s ≫ e.inv)]
      at hs
    exact ((key _).2 hs).summable

theorem SumsCompatible.pred_map_ovee {X : D'} {p q : X ⟶ I'} (h : Perp p q) :
    F.map (ovee p q h) ≫ e.hom =
      ovee (F.map p ≫ e.hom) (F.map q ≫ e.hom) ((hsum.pred_perp_iff I' e p q).1 h) := by
  have := (hsum.pred_sumsTo_iff I' e _ _).1 (sumsTo_sum h)
  have e2 : (fun j => F.map (![p, q] j) ≫ e.hom) = ![F.map p ≫ e.hom, F.map q ≫ e.hom] := by
    funext i; fin_cases i <;> rfl
  rw [e2] at this
  exact (this.sum_eq _).symm

theorem SumsCompatible.pred_inj {X : D'} {p q : X ⟶ I'}
    (h : F.map p ≫ e.hom = F.map q ≫ e.hom) : p = q :=
  F.map_injective (by simpa using congrArg (· ≫ e.inv) h)

/-- The σ-effectus structure of `D'` transported along `F` (fully faithful,
preserving countable coproducts and sums, with `F I' ≅ I`). -/
noncomputable def SumsCompatible.sigmaEffectus
    (hpres : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F) :
    SigmaEffectus D' :=
  { hsum.sigmaPAC hpres with
    «I» := I'
    one := fun X => F.preimage (SigmaEffectus.one (F.obj X) ≫ e.inv)
    orth := fun {X} p => F.preimage (SigmaEffectus.orth (F.map p ≫ e.hom) ≫ e.inv)
    perp_orth := fun {X} p => by
      rw [hsum.pred_perp_iff I' e, F.map_preimage, Category.assoc, e.inv_hom_id,
        Category.comp_id]
      exact SigmaEffectus.perp_orth _
    ovee_orth := fun {X} p => by
      apply hsum.pred_inj I' e
      rw [hsum.pred_map_ovee I' e]
      have h1 : F.map (F.preimage (SigmaEffectus.orth (F.map p ≫ e.hom) ≫ e.inv)) ≫ e.hom =
          SigmaEffectus.orth (F.map p ≫ e.hom) := by
        rw [F.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
      have h2 : F.map (F.preimage (SigmaEffectus.one (F.obj X) ≫ e.inv)) ≫ e.hom =
          SigmaEffectus.one (F.obj X) := by
        rw [F.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
      rw [h2]
      exact (PCM.ovee_congr rfl h1 _ (SigmaEffectus.perp_orth _)).trans
        (SigmaEffectus.ovee_orth _)
    orth_unique := fun {X p q} h hpq => by
      apply hsum.pred_inj I' e
      rw [F.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
      refine SigmaEffectus.orth_unique ((hsum.pred_perp_iff I' e p q).1 h) ?_
      rw [← hsum.pred_map_ovee I' e h, hpq, F.map_preimage, Category.assoc, e.inv_hom_id,
        Category.comp_id]
    eq_zero_of_perp_one := fun {X p} h => by
      rw [hsum.pred_perp_iff I' e, F.map_preimage, Category.assoc, e.inv_hom_id,
        Category.comp_id] at h
      apply hsum.pred_inj I' e
      rw [SigmaEffectus.eq_zero_of_perp_one h, hsum.map_zero]
      exact (FinPAC.zero_comp _).symm
    eq_zero_of_one_zero := fun {X Y f} h => by
      have h1 := congrArg (fun k => F.map k ≫ e.hom) h
      simp only [F.map_comp, Category.assoc, F.map_preimage, e.inv_hom_id, Category.comp_id,
        hsum.map_zero] at h1
      apply F.map_injective
      rw [hsum.map_zero]
      refine SigmaEffectus.eq_zero_of_one_zero ?_
      rw [h1]; exact FinPAC.zero_comp _
    perp_of_one_perp := fun {X Y f g} h => by
      rw [hsum.pred_perp_iff I' e] at h
      simp only [F.map_comp, Category.assoc, F.map_preimage, e.inv_hom_id,
        Category.comp_id] at h
      exact (hsum.perp_iff f g).2 (SigmaEffectus.perp_of_one_perp h) }

end TransportEffectus

section TransportMorphism

variable {D : Type u} [Category.{v} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasCountableCoproducts D']
  [∀ X Y : D', SigmaPAM (X ⟶ Y)]
variable {F : D' ⥤ D} [F.Full] [F.Faithful] (hsum : SumsCompatible F)
  (I' : D') (e : F.obj I' ≅ SigmaEffectus.«I» (C := D))
  (hpres : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) F)

/-- `F` is a morphism of σ-effectuses for the transported structure. -/
noncomputable def SumsCompatible.morphism :
    @SigmaEffectusMorphism D' _ _ _ (hsum.sigmaEffectus I' e hpres) D _ _ _ _ :=
  letI := hsum.sigmaEffectus I' e hpres
  { F := F
    preserves := hpres
    u := e.symm
    map_truth := fun A => by
      show F.map (F.preimage (SigmaEffectus.one (F.obj A) ≫ e.inv)) = _
      rw [F.map_preimage]; rfl }

end TransportMorphism

section MorphismComp

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
variable {D : Type u₂} [Category.{v₂} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {E : Type u₃} [Category.{v₃} E] [HasCountableCoproducts E]
  [∀ X Y : E, SigmaPAM (X ⟶ Y)] [SigmaEffectus E]

/-- The composite of morphisms of σ-effectuses. -/
noncomputable def sigmaMorphismComp (Φ : SigmaEffectusMorphism C D)
    (Ψ : SigmaEffectusMorphism D E) : SigmaEffectusMorphism C E where
  F := Φ.F ⋙ Ψ.F
  preserves J _ := by
    have := Φ.preserves J
    have := Ψ.preserves J
    infer_instance
  u := Ψ.u ≪≫ Ψ.F.mapIso Φ.u
  map_truth A := by
    simp only [Functor.comp_obj, Functor.comp_map, Φ.map_truth, Ψ.F.map_comp, Ψ.map_truth,
      Iso.trans_hom, Functor.mapIso_hom, Category.assoc]

end MorphismComp

section Lift

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
variable {D : Type u₂} [Category.{v₂} D] [HasCountableCoproducts D]
  [∀ X Y : D, SigmaPAM (X ⟶ Y)] [SigmaEffectus D]
variable {D' : Type u₃} [Category.{v₃} D'] [HasCountableCoproducts D']
  [∀ X Y : D', SigmaPAM (X ⟶ Y)] [SigmaEffectus D']
variable (G : SigmaEffectusMorphism D' D) [G.F.Full] [G.F.Faithful]
  (Φ : SigmaEffectusMorphism C D) (h : ∀ A : C, ∃ Y : D', Nonempty (G.F.obj Y ≅ Φ.F.obj A))

/-- The lift of `Φ` through the fully faithful `G`, as a functor. -/
noncomputable def liftFunctor : C ⥤ D' where
  obj A := (h A).choose
  map {A B} f := G.F.preimage ((h A).choose_spec.some.hom ≫ Φ.F.map f ≫
    (h B).choose_spec.some.inv)
  map_id A := G.F.map_injective (by simp)
  map_comp f g := G.F.map_injective (by simp)

/-- `liftFunctor ⋙ G ≅ Φ`. -/
noncomputable def liftIso : liftFunctor G Φ h ⋙ G.F ≅ Φ.F :=
  NatIso.ofComponents (fun A => (h A).choose_spec.some) (fun {A B} f => by
    simp [liftFunctor])

/-- The lift of a morphism of σ-effectuses whose objects lie in the essential
image of a fully faithful morphism of σ-effectuses `G`. -/
noncomputable def liftMorphism : SigmaEffectusMorphism C D' where
  F := liftFunctor G Φ h
  preserves J _ := by
    have := Φ.preserves J
    have := G.preserves J
    have : PreservesColimitsOfShape (Discrete J) (liftFunctor G Φ h ⋙ G.F) :=
      preservesColimitsOfShape_of_natIso (liftIso G Φ h).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _ G.F
  u := G.F.preimageIso (G.u.symm ≪≫ Φ.u ≪≫ ((h (effObj C)).choose_spec.some).symm)
  map_truth A := by
    apply G.F.map_injective
    simp only [liftFunctor, Functor.map_preimage, Functor.map_comp, Functor.preimageIso_hom,
      Iso.trans_hom, Iso.symm_hom, Φ.map_truth, G.map_truth, Category.assoc]
    have hT := iso_isTotal ((h A).choose_spec.some.hom)
    rw [← Category.assoc ((h A).choose_spec.some.hom), hT]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem liftMorphism_faithful [Φ.F.Faithful] : (liftMorphism G Φ h).F.Faithful :=
  ⟨fun {A B} f g hfg => by
    have := congrArg G.F.map hfg
    simp only [liftMorphism, liftFunctor, Functor.map_preimage] at this
    exact Φ.F.map_injective (by simpa using this)⟩

end Lift

/-! ## Restriction of scalars along an effect-monoid isomorphism -/

section Restrict

variable {M N : Type u} [EffectMonoid M] [EffectMonoid N]

theorem emHom_isAdditive (φ : EffectMonoidHom M N) : IsAdditive φ.toFun :=
  ⟨emHom_map_zero φ, fun h => ⟨φ.perp_map h, (φ.ovee_map h).symm⟩⟩

theorem IsSigmaAdditiveC.comp {X Y Z : Type u} [EffectAlgebra X] [EffectAlgebra Y]
    [EffectAlgebra Z] {f : X → Y} {g : Y → Z} (hf : IsSigmaAdditiveC f)
    (hg : IsSigmaAdditiveC g) : IsSigmaAdditiveC (g ∘ f) :=
  fun J _ x s h => hg J _ _ (hf J x s h)

variable (φ : EffectMonoidHom M N) (hφ : IsSigmaAdditiveC φ.toFun)

/-- An `N`-module as an `M`-module along `φ : M → N`. -/
def restrictModule (E : Type u) [EffectAlgebra E] [EffectModule N E] : EffectModule M E where
  smul r x := φ.toFun r • x
  mul_smul l m a := by
    show φ.toFun (l * m) • a = φ.toFun l • φ.toFun m • a
    rw [φ.map_mul, EffectModule.mul_smul]
  smul_perp l _ _ h := EffectModule.smul_perp (φ.toFun l) h
  perp_smul {l m} h a := by
    obtain ⟨h', e⟩ := EffectModule.perp_smul (φ.perp_map h) a
    refine ⟨h', ?_⟩
    show ovee (φ.toFun l • a) (φ.toFun m • a) h' = φ.toFun (ovee l m h) • a
    rw [e, φ.ovee_map h]
  one_smul a := by
    show φ.toFun 1 • a = a
    rw [φ.map_one, EffectModule.one_smul]

/-- A σ-effect `N`-module as a σ-effect `M`-module along a σ-additive `φ`. -/
def restrictObj (X : SEMod N) : SEMod M :=
  @SEMod.mk M _ X.carrier X.ea (restrictModule φ X.carrier)
    ⟨X.sigma.1, fun r => X.sigma.2.1 (φ.toFun r), fun a => hφ.comp (X.sigma.2.2 a)⟩

/-- Restriction of scalars `sEMod[N] → sEMod[M]`. -/
def restrictFunctor : SEMod N ⥤ SEMod M where
  obj := restrictObj φ hφ
  map {X Y} f := ⟨f.toFun, f.additive, fun r a => f.map_smul (φ.toFun r) a, f.sigma⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable (ψ : EffectMonoidHom N M) (hψ : IsSigmaAdditiveC ψ.toFun)
  (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a) (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b)

instance restrictFunctor_faithful : (restrictFunctor φ hφ).Faithful :=
  ⟨fun {X Y} f g h => SEMod.hom_ext fun a =>
    congrArg (fun k : restrictObj φ hφ X ⟶ restrictObj φ hφ Y => k.toFun a) h⟩

include hφψ in
theorem restrictFunctor_full : (restrictFunctor φ hφ).Full :=
  ⟨fun {X Y} g => ⟨⟨g.toFun, g.additive, fun s (a : X.carrier) => by
      have := g.map_smul (ψ.toFun s) a
      change g.toFun (φ.toFun (ψ.toFun s) • a) =
        φ.toFun (ψ.toFun s) • (show Y.carrier from g.toFun a) at this
      rwa [hφψ] at this, g.sigma⟩, rfl⟩⟩

include hψ hψφ in
theorem restrictFunctor_essSurj : (restrictFunctor φ hφ).EssSurj :=
  ⟨fun Y => ⟨restrictObj ψ hψ Y, ⟨
    { hom := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun r a =>
          congrArg (fun t : M => t • (show Y.carrier from a)) (hψφ r), fun _ _ _ _ h => h⟩
      inv := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun r a =>
          (congrArg (fun t : M => t • (show Y.carrier from a)) (hψφ r)).symm,
          fun _ _ _ _ h => h⟩
      hom_inv_id := rfl
      inv_hom_id := rfl }⟩⟩⟩

include hψ hψφ hφψ in
theorem restrictFunctor_isEquivalence : (restrictFunctor φ hφ).IsEquivalence :=
  { full := restrictFunctor_full φ hφ ψ hφψ
    essSurj := restrictFunctor_essSurj φ hφ ψ hψ hψφ }

variable (hM : IsSigmaEffectMonoid M) (hN : IsSigmaEffectMonoid N)

/-- `restrict_φ (N) ≅ M` via `ψ`. -/
def restrictUnitIso : restrictObj φ hφ (SEMod.unit N hN) ≅ SEMod.unit M hM where
  hom := ⟨ψ.toFun, emHom_isAdditive ψ, fun r (s : N) => by
      show ψ.toFun (φ.toFun r * s) = r * ψ.toFun s
      rw [ψ.map_mul, hψφ], hψ⟩
  inv := ⟨φ.toFun, emHom_isAdditive φ, fun r (s : M) => φ.map_mul r s, hφ⟩
  hom_inv_id := SEMod.hom_ext fun s => hφψ s
  inv_hom_id := SEMod.hom_ext fun s => hψφ s

include hψ hψφ hφψ in
/-- Restriction of scalars along an isomorphism of σ-effect monoids is a
morphism of σ-effectuses `sEMod[N]ᵒᵖ → sEMod[M]ᵒᵖ`. -/
noncomputable def restrictMorphism :
    @SigmaEffectusMorphism (SEMod N)ᵒᵖ _ _ _ (SEMod.sigmaEffectus hN)
      (SEMod M)ᵒᵖ _ _ _ (SEMod.sigmaEffectus hM) :=
  letI := SEMod.sigmaEffectus hN
  letI := SEMod.sigmaEffectus hM
  haveI := restrictFunctor_isEquivalence φ hφ ψ hψ hψφ hφψ
  { F := (restrictFunctor φ hφ).op
    preserves := fun _ _ => inferInstance
    u := (restrictUnitIso φ hφ ψ hψ hψφ hφψ hM hN).op
    map_truth := fun A => by
      apply Quiver.Hom.unop_inj
      refine SEMod.hom_ext fun (s : N) => ?_
      show s • (1 : A.unop.carrier) = φ.toFun (ψ.toFun s) • (1 : A.unop.carrier)
      rw [hφψ] }

end Restrict

/-! ## `sBOUSᵒᵖ` is a σ-effectus -/

section SBOUSEffectus

/-- `sEMod[[0,1]]ᵒᵖ` with its σ-effectus structure (SIG 28/63). -/
noncomputable instance semodI_sigmaEffectus : SigmaEffectus (SEMod I)ᵒᵖ :=
  SEMod.sigmaEffectus unitInterval_isSigmaEffectMonoid

instance sbousFunctor_isEquivalence : sbousFunctor.IsEquivalence := sig55

/-- `sBOUSᵒᵖ` has countable coproducts (those of `sEMod[[0,1]]ᵒᵖ`, i.e. the
products of `sEMod[[0,1]]`, through SIG 55). -/
instance : HasCountableCoproducts SBOUSᵒᵖ :=
  ⟨fun _ _ => Adjunction.hasColimitsOfShape_of_equivalence sbousFunctor.op⟩

/-- The hom-sets of `sBOUSᵒᵖ` as σ-PAMs: pointwise sums on the unit
intervals (transported along SIG 55). -/
noncomputable instance sbousHomPAM (X Y : SBOUSᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  SigmaPAM.ofEquiv ((Functor.FullyFaithful.ofFullyFaithful sbousFunctor.op).homEquiv)

theorem sbous_sumsCompatible : SumsCompatible sbousFunctor.op :=
  fun x s => SigmaPAM.ofEquiv_sumsTo_iff _ x s

/-- The unit object of `sBOUSᵒᵖ` (the Gudder–Pulmannová space of `[0,1]`,
isomorphic to `ℝ`). -/
noncomputable def sbousUnit : SBOUSᵒᵖ :=
  op (gpSBOUS (SEMod.unit I unitInterval_isSigmaEffectMonoid))

noncomputable def sbousUnitIso :
    sbousFunctor.op.obj sbousUnit ≅ SigmaEffectus.«I» (C := (SEMod I)ᵒᵖ) :=
  (SEMod.isoOfEMod (gpIso (EModS.mk (SEMod.unit I unitInterval_isSigmaEffectMonoid).carrier))).symm.op

/-- **SIG 55** (main.tex:1554): "This proves that `sBOUSᵒᵖ` is a
σ-effectus": the σ-effectus structure transported along SIG 55. -/
noncomputable instance sbous_sigmaEffectus : SigmaEffectus SBOUSᵒᵖ :=
  sbous_sumsCompatible.sigmaEffectus sbousUnit sbousUnitIso (fun _ _ => inferInstance)

/-- `sBOUSᵒᵖ → sEMod[[0,1]]ᵒᵖ`, `A ↦ [0,u]_A`, is a morphism of σ-effectuses. -/
noncomputable def sbousMorphism : SigmaEffectusMorphism SBOUSᵒᵖ (SEMod I)ᵒᵖ :=
  sbous_sumsCompatible.morphism sbousUnit sbousUnitIso (fun _ _ => inferInstance)

end SBOUSEffectus

/-! ## SIG 56: the probabilistic case, predicates -/

section SIG56

variable {C : Type} [Category.{0} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- **SIG 56** (`thm:convex-effectus-embedding`, main.tex:1560, Theorem): a
predicate-separated σ-effectus with scalars `C(I,I) ≅ [0,1]` has a faithful
morphism of σ-effectuses `F : C → sBOUSᵒᵖ`, with `Pred(A) ≅ [0,u]_{FA}` (as
σ-effect modules over the scalars, which act on `[0,u]_{FA}` through the
isomorphism).  Proof as printed: SIG 37 (`Pred` is faithful), SIG 64 (`Pred`
is a morphism of σ-effectuses into `sEMod[C(I,I)]ᵒᵖ ≅ sEMod[[0,1]]ᵒᵖ`) and
SIG 55.  Stated for a small `C` (`C : Type`, hom-sets in `Type`), so that
its predicate modules live in the universe of `sBOUS`. -/
theorem sig56 (hsep : PredicateSeparated C) (φ : EffectMonoidHom (Scal C) I)
    (ψ : EffectMonoidHom I (Scal C)) (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a)
    (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) :
    ∃ (F : SigmaEffectusMorphism C SBOUSᵒᵖ)
      (hφ : IsSigmaAdditiveC φ.toFun), F.F.Faithful ∧
      ∀ A : C, Nonempty (predObj A ≅ restrictObj φ hφ (sbousObj (F.F.obj A).unop)) := by
  let _ := SEMod.sigmaEffectus (scal_isSigmaEffectMonoid (C := C))
  have hφ : IsSigmaAdditiveC φ.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive φ) (emHom_isAdditive ψ) hψφ hφψ
  have hψ : IsSigmaAdditiveC ψ.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive ψ) (emHom_isAdditive φ) hφψ hψφ
  let B := restrictMorphism φ hφ ψ hψ hψφ hφψ (scal_isSigmaEffectMonoid (C := C))
    unitInterval_isSigmaEffectMonoid
  let G := sigmaMorphismComp sbousMorphism B
  have := restrictFunctor_isEquivalence φ hφ ψ hψ hψφ hφψ
  have : G.F.IsEquivalence := by
    show (sbousFunctor.op ⋙ (restrictFunctor φ hφ).op).IsEquivalence
    infer_instance
  have hpred : (predFunctor (C := C)).Faithful := (predicateSeparated_iff_faithful).1 hsep
  let Φ := predMorphism (C := C)
  have h : ∀ A : C, ∃ Y : SBOUSᵒᵖ, Nonempty (G.F.obj Y ≅ Φ.F.obj A) :=
    fun A => ⟨G.F.objPreimage (Φ.F.obj A), ⟨G.F.objObjPreimageIso _⟩⟩
  refine ⟨liftMorphism G Φ h, hφ, ?_, fun A => ?_⟩
  · have : Φ.F.Faithful := hpred
    exact liftMorphism_faithful G Φ h
  · exact ⟨((liftIso G Φ h).app A).unop⟩

end SIG56

/-! ## Countable coproducts along a fully faithful functor -/

section FFCoproducts

variable {D : Type u} [Category.{v} D] [HasCountableCoproducts D]
variable {D' : Type u₂} [Category.{v₂} D'] (F : D' ⥤ D) [F.Full] [F.Faithful]
  (hcop : ∀ (J : Type) [Countable J] (X : J → D'),
    ∃ Y : D', Nonempty (F.obj Y ≅ ∐ fun j => F.obj (X j)))

/-- The cofan in `D'` over `X` whose image is a coproduct in `D`. -/
noncomputable def ffCofan {J : Type} [Countable J] (X : J → D') : Cofan X :=
  Cofan.mk (hcop J X).choose fun j =>
    F.preimage (Sigma.ι (fun j => F.obj (X j)) j ≫ (hcop J X).choose_spec.some.inv)

/-- Its image under `F` is a colimit. -/
noncomputable def ffCofan_mapIsColimit {J : Type} [Countable J] (X : J → D') :
    IsColimit (F.mapCocone (ffCofan F hcop X)) where
  desc s := (hcop J X).choose_spec.some.hom ≫ Sigma.desc fun j => s.ι.app ⟨j⟩
  fac s := by
    rintro ⟨j⟩
    simp [ffCofan]
  uniq s m hm := by
    have key : (hcop J X).choose_spec.some.inv ≫ m = Sigma.desc fun j => s.ι.app ⟨j⟩ := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have := hm ⟨j⟩
      simp only [Functor.mapCocone_ι_app, ffCofan, Cofan.mk_ι_app, Functor.map_preimage] at this
      rw [Sigma.ι_desc]
      exact (Category.assoc _ _ _).symm.trans this
    exact (Iso.inv_comp_eq _).1 key

noncomputable def ffCofan_isColimit {J : Type} [Countable J] (X : J → D') :
    IsColimit (ffCofan F hcop X) :=
  isColimitOfReflects F (ffCofan_mapIsColimit F hcop X)

include hcop in
theorem hasCountableCoproducts_of_ff : HasCountableCoproducts D' :=
  ⟨fun J _ => ⟨fun K => by
    have : HasColimit (Discrete.functor (K.obj ∘ Discrete.mk)) :=
      ⟨⟨⟨_, ffCofan_isColimit F hcop (K.obj ∘ Discrete.mk)⟩⟩⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor⟩⟩

include hcop in
theorem preserves_of_ff (J : Type) [Countable J] : PreservesColimitsOfShape (Discrete J) F := by
  constructor
  intro K
  have key : ∀ X : J → D', PreservesColimit (Discrete.functor X) F := fun X =>
    preservesColimit_of_preserves_colimit_cocone (ffCofan_isColimit F hcop X)
      (ffCofan_mapIsColimit F hcop X)
  have := key (K.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

end FFCoproducts

/-! ## Restriction of scalars for σ-weight modules -/

section RestrictSW

variable {M N : Type u} [EffectMonoid M] [EffectMonoid N]
  (φ : EffectMonoidHom M N) (hφ : IsSigmaAdditiveC φ.toFun)
  (ψ : EffectMonoidHom N M) (hψ : IsSigmaAdditiveC ψ.toFun)
  (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a) (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b)

theorem CSummable.map {X Y : Type u} [EffectAlgebra X] [EffectAlgebra Y] {f : X → Y}
    (hf : IsAdditive f) {J : Type} {x : J → X} (h : CSummable x) :
    CSummable (fun j => f (x j)) := fun F => by
  obtain ⟨s, hs⟩ := h F
  exact ⟨_, hf.finSum hs⟩

include hφ hψ hψφ hφψ in
/-- A σ-weight `N`-module as a σ-weight `M`-module along `φ` (weights through
`ψ = φ⁻¹`). -/
def restrictSWObj (X : SWMod N) : SWMod M :=
  @SWMod.mk M _ X.carrier X.pam ⟨fun r x => φ.toFun r • x⟩ (fun x => ψ.toFun (X.weight x))
    (fun x => by
      show φ.toFun 1 • x = x
      rw [φ.map_one, X.one_smul])
    (fun r s x => by
      show φ.toFun (r * s) • x = φ.toFun r • φ.toFun s • x
      rw [φ.map_mul, X.mul_smul])
    (fun x J _ r s h => X.smul_left x (fun j => φ.toFun (r j)) (φ.toFun s) (hφ J r s h))
    (fun r J _ x s h => X.smul_right (φ.toFun r) x s h)
    (fun x s h => hψ _ _ _ (X.weight_sumsTo x s h))
    (fun r x => by
      show ψ.toFun (X.weight (φ.toFun r • x)) = r * ψ.toFun (X.weight x)
      rw [X.weight_smul, ψ.map_mul, hψφ])
    (fun x h => X.eq_zero_of_weight x (by
      have := congrArg φ.toFun h
      rwa [hφψ, emHom_map_zero] at this))
    (fun x h => X.summable_of_weight x (by
      have := CSummable.map (emHom_isAdditive φ) h
      simpa only [hφψ] using this))

/-- Restriction of scalars `sWMod[N] → sWMod[M]`. -/
def restrictSWFunctor : SWMod N ⥤ SWMod M where
  obj := restrictSWObj φ hφ ψ hψ hψφ hφψ
  map {X Y} f := ⟨f.toFun, fun x s h => f.sigma x s h, fun r x => f.map_smul (φ.toFun r) x,
    fun x => (additive_subunital ψ.toFun (emHom_isAdditive ψ)).2 _ _ (f.weight_le x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance restrictSWFunctor_faithful : (restrictSWFunctor φ hφ ψ hψ hψφ hφψ).Faithful :=
  ⟨fun {X Y} f g h => SWMod.hom_ext fun a =>
    congrArg (fun k : restrictSWObj φ hφ ψ hψ hψφ hφψ X ⟶ restrictSWObj φ hφ ψ hψ hψφ hφψ Y =>
      k.toFun a) h⟩

theorem restrictSWFunctor_full : (restrictSWFunctor φ hφ ψ hψ hψφ hφψ).Full :=
  ⟨fun {X Y} g => ⟨⟨g.toFun, fun x s h => g.sigma x s h, fun s (a : X.carrier) => by
      have := g.map_smul (ψ.toFun s) a
      change g.toFun (φ.toFun (ψ.toFun s) • a) =
        φ.toFun (ψ.toFun s) • (show Y.carrier from g.toFun a) at this
      rwa [hφψ] at this,
    fun x => by
      have := (additive_subunital φ.toFun (emHom_isAdditive φ)).2 _ _ (g.weight_le x)
      change φ.toFun (ψ.toFun (Y.weight (g.toFun x))) ≼ φ.toFun (ψ.toFun (X.weight x)) at this
      rwa [hφψ, hφψ] at this⟩, rfl⟩⟩

/-- Restricting along `ψ` and back along `φ` is the identity. -/
def restrictSWRoundTrip (Y : SWMod M) :
    restrictSWObj φ hφ ψ hψ hψφ hφψ (restrictSWObj ψ hψ φ hφ hφψ hψφ Y) ≅ Y where
  hom := ⟨id, fun _ _ h => h, fun r a =>
      congrArg (fun t : M => t • (show Y.carrier from a)) (hψφ r),
      fun a => by
        show Y.weight a ≼ ψ.toFun (φ.toFun (Y.weight a))
        rw [hψφ]; exact pcm_preorder_refl _⟩
  inv := ⟨id, fun _ _ h => h, fun r a =>
      (congrArg (fun t : M => t • (show Y.carrier from a)) (hψφ r)).symm,
      fun a => by
        show ψ.toFun (φ.toFun (Y.weight a)) ≼ Y.weight a
        rw [hψφ]; exact pcm_preorder_refl _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem restrictSWFunctor_essSurj : (restrictSWFunctor φ hφ ψ hψ hψφ hφψ).EssSurj :=
  ⟨fun Y => ⟨restrictSWObj ψ hψ φ hφ hφψ hψφ Y, ⟨restrictSWRoundTrip φ hφ ψ hψ hψφ hφψ Y⟩⟩⟩

theorem restrictSWFunctor_isEquivalence : (restrictSWFunctor φ hφ ψ hψ hψφ hφψ).IsEquivalence :=
  { full := restrictSWFunctor_full φ hφ ψ hψ hψφ hφψ
    essSurj := restrictSWFunctor_essSurj φ hφ ψ hψ hψφ hφψ }

variable [hM : Fact (IsSigmaEffectMonoid M)] [hN : Fact (IsSigmaEffectMonoid N)]

/-- `restrict_φ (N) ≅ M` via `ψ`. -/
noncomputable def restrictSWUnitIso :
    SWMod.unit M hM.out ≅ restrictSWObj φ hφ ψ hψ hψφ hφψ (SWMod.unit N hN.out) where
  hom := ⟨φ.toFun, fun x s h => by
      have := (SWMod.unit_sumsTo_iff (M := M) x s).1 h
      exact (SWMod.unit_sumsTo_iff (M := N) _ _).2 (hφ _ x s this),
    fun r (s : M) => φ.map_mul r s,
    fun (s : M) => by
      show ψ.toFun (φ.toFun s) ≼ s
      rw [hψφ]; exact pcm_preorder_refl _⟩
  inv := ⟨ψ.toFun, fun x s h => by
      have := (SWMod.unit_sumsTo_iff (M := N) x s).1 h
      exact (SWMod.unit_sumsTo_iff (M := M) _ _).2 (hψ _ x s this),
    fun r (s : N) => by
      show ψ.toFun (φ.toFun r * s) = r * ψ.toFun s
      rw [ψ.map_mul, hψφ],
    fun (s : N) => pcm_preorder_refl _⟩
  hom_inv_id := SWMod.hom_ext fun s => hψφ s
  inv_hom_id := SWMod.hom_ext fun s => hφψ s

/-- Restriction of scalars along an isomorphism of σ-effect monoids is a
morphism of σ-effectuses `sWMod[N] → sWMod[M]`. -/
noncomputable def restrictSWMorphism : SigmaEffectusMorphism (SWMod N) (SWMod M) :=
  haveI := restrictSWFunctor_isEquivalence φ hφ ψ hψ hψφ hφψ
  { F := restrictSWFunctor φ hφ ψ hψ hψφ hφψ
    preserves := fun _ _ => inferInstance
    u := restrictSWUnitIso φ hφ ψ hψ hψφ hφψ
    map_truth := fun A => SWMod.hom_ext fun x => by
      show A.weight x = φ.toFun (ψ.toFun (A.weight x))
      rw [hφψ] }

end RestrictSW

/-! ## Effect-monoid maps to `[0,1]` from the opposite monoid -/

section MOpHom

variable {M : Type u} [EffectMonoid M]

theorem unitInterval_mul_comm (a b : I) : a * b = b * a :=
  Subtype.ext (by rw [GP.I_coe_mul, GP.I_coe_mul, mul_comm])

/-- A map of effect monoids `M → [0,1]` is one `Mᵒᵖ → [0,1]` (`[0,1]` is
commutative). -/
def emHomToMOp (φ : EffectMonoidHom M I) : EffectMonoidHom (MOp M) I where
  toFun := φ.toFun
  perp_map := φ.perp_map
  ovee_map := φ.ovee_map
  map_one := φ.map_one
  map_mul a b := by
    show φ.toFun (@HMul.hMul M M M instHMul b a) = φ.toFun a * φ.toFun b
    exact (φ.map_mul b a).trans (unitInterval_mul_comm _ _)

/-- A map of effect monoids `[0,1] → M` is one `[0,1] → Mᵒᵖ`. -/
def emHomFromMOp (ψ : EffectMonoidHom I M) : EffectMonoidHom I (MOp M) where
  toFun := ψ.toFun
  perp_map := ψ.perp_map
  ovee_map := ψ.ovee_map
  map_one := ψ.map_one
  map_mul a b := by
    show ψ.toFun (a * b) = @HMul.hMul M M M instHMul (ψ.toFun b) (ψ.toFun a)
    rw [unitInterval_mul_comm]
    exact ψ.map_mul b a

end MOpHom

end Papers.SIG

open scoped NNReal

/-!
# SIG §5.2 / App. C, weight side (points SIG 57, 58, 59, 73)

Ordered vector spaces with trace, subbases, (cancellative) weight
`[0,1]`-modules, the base norm, and the equivalences `OVSt ≃ CWMod[[0,1]]`
(SIG 58) and `sBBNS ≃ sCWMod[[0,1]]` (SIG 59), with SIG 73 (a σ-structure on
the subbase makes `V` a Banach pre-base-norm space).

* Finite weight `[0,1]`-modules are the class `WeightMod` over the tree's
  `PCM`; `CWMod` bundles the cancellative ones.
* `V(X)` for a cancellative weight module `X` (SIG 58's inverse) is built in
  namespace `CW` as formal multiples `r · a` modulo rescaling, then formal
  differences: the tree's Gudder–Pulmannová construction (179III.2), whose
  sums are here total because weights add up to at most `1`.
* The base norm is `OVSt.bnorm`; on `V ∈ sBBNS` it is made a `NormedSpace`
  locally (`SBBNS.nag`, `SBBNS.nsp`), and the σ-PAM of the subbase is the sum
  of (unconditionally, absolutely convergent) series.
-/

namespace Papers.SIG

universe uw

/-! ## SIG 57: finite weight `[0,1]`-modules

The finite (PCM) version of SIG 30 at `M = [0,1]`: the action and the weight
are spelled out as fields, as the tree's `EffectModule` does. -/

/-- **SIG 57** (main.tex:1598, Definition, text; SIG 30 at `M = [0,1]`):
a **weight `[0,1]`-module**: a PCM `X` with a biadditive `[0,1]`-action and an
additive, action-preserving weight `|·| : X → [0,1]` such that `|x| = 0`
implies `x = 0` and `|x| ⊥ |y|` (i.e. `|x| + |y| ≤ 1`) implies `x ⊥ y`. -/
class WeightMod (X : Type uw) [PCM X] extends SMul I X where
  wt : X → I
  mul_smul : ∀ (l m : I) (a : X), (l * m) • a = l • m • a
  one_smul : ∀ a : X, (1 : I) • a = a
  smul_perp : ∀ (l : I) {a b : X} (h : Perp a b),
    ∃ h' : Perp (l • a) (l • b), ovee (l • a) (l • b) h' = l • ovee a b h
  perp_smul : ∀ {l m : I} (h : Perp l m) (a : X),
    ∃ h' : Perp (l • a) (m • a), ovee (l • a) (m • a) h' = ovee l m h • a
  smul_zero : ∀ l : I, l • (0 : X) = 0
  zero_smul : ∀ a : X, (0 : I) • a = 0
  wt_zero : wt 0 = 0
  wt_ovee : ∀ {a b : X} (h : Perp a b), ((wt (ovee a b h) : I) : ℝ) = (wt a : ℝ) + wt b
  wt_smul : ∀ (l : I) (a : X), wt (l • a) = l * wt a
  eq_zero_of_wt : ∀ a : X, wt a = 0 → a = 0
  perp_of_wt : ∀ {a b : X}, (wt a : ℝ) + wt b ≤ 1 → Perp a b

export WeightMod (wt)

/-- **SIG 57** (main.tex:1596, Definition, text): a weight module is **cancellative** if
`x ⊕ y = x ⊕ z` implies `y = z`. -/
def WeightMod.Cancellative (X : Type uw) [PCM X] [WeightMod X] : Prop :=
  ∀ {x y z : X} (hy : Perp x y) (hz : Perp x z), ovee x y hy = ovee x z hz → y = z

namespace CW

variable {X : Type uw} [PCM X] [WeightMod X]

theorem perp_iff_wt {a b : X} : Perp a b ↔ (wt a : ℝ) + wt b ≤ 1 := by
  refine ⟨fun h => ?_, WeightMod.perp_of_wt⟩
  rw [← WeightMod.wt_ovee h]; exact (wt (ovee a b h)).2.2

theorem wt_le_of_le {l : I} (a : X) : ((wt (l • a) : I) : ℝ) ≤ l := by
  rw [WeightMod.wt_smul, GP.I_coe_mul]
  exact mul_le_of_le_one_right l.2.1 (wt a).2.2

theorem smul_perp_smul {l m : I} (hlm : Perp l m) (a b : X) : Perp (l • a) (m • b) := by
  rw [perp_iff_wt]
  have := GP.I_perp_iff.1 hlm
  linarith [wt_le_of_le (l := l) a, wt_le_of_le (l := m) b]

/-- The weight is additive and preserves the action (the printed
conditions), and the action is biadditive. -/
theorem weightMod_print :
    IsBiadditive (fun (r : I) (a : X) => r • a) ∧ IsAdditive (WeightMod.wt (X := X)) := by
  refine ⟨⟨fun r => ⟨WeightMod.smul_zero r, fun h => ?_⟩,
    fun a => ⟨WeightMod.zero_smul a, fun h => ?_⟩⟩, WeightMod.wt_zero, fun h => ?_⟩
  · obtain ⟨h', e⟩ := WeightMod.smul_perp r h; exact ⟨h', e⟩
  · obtain ⟨h', e⟩ := WeightMod.perp_smul h a; exact ⟨h', e⟩
  · rename_i a b
    have hp : Perp (wt a) (wt b) := by
      rw [GP.I_perp_iff, ← WeightMod.wt_ovee h]; exact (wt (ovee _ _ h)).2.2
    exact ⟨hp, Subtype.ext (by rw [GP.I_coe_ovee, WeightMod.wt_ovee h])⟩

/-- A nonzero scalar acts injectively (the `1/n` trick, as in the tree's
`GP.smul_left_cancel`). -/
theorem smul_left_cancel {l : I} (hl : l ≠ 0) {a b : X} (h : l • a = l • b) : a = b := by
  obtain ⟨n, c, hn1, hcl⟩ := GP.exists_nat_scale hl
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have key0 : GP.Iv (1 / (n : ℝ)) • a = GP.Iv (1 / (n : ℝ)) • b := by
    rw [← hcl, mul_comm l c, WeightMod.mul_smul, WeightMod.mul_smul, h]
  have h1n0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have key : ∀ k : ℕ, (k : ℝ) ≤ (n : ℝ) →
      GP.Iv ((k : ℝ) / (n : ℝ)) • a = GP.Iv ((k : ℝ) / (n : ℝ)) • b := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_div, GP.Iv_zero, WeightMod.zero_smul a, WeightMod.zero_smul b]
    | succ k ih =>
      intro hk
      rw [Nat.cast_succ] at hk
      have hk' : (k : ℝ) ≤ (n : ℝ) := by linarith
      have hkn0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
      have hsum : (k : ℝ) / (n : ℝ) + 1 / (n : ℝ) ≤ 1 := by
        rw [← add_div, div_le_one hn0]; linarith
      have hp := GP.Iv_perp hkn0 h1n0 hsum
      obtain ⟨ha', ea⟩ := WeightMod.perp_smul hp a
      obtain ⟨hb', eb⟩ := WeightMod.perp_smul hp b
      rw [GP.Iv_ovee hkn0 h1n0 hsum hp] at ea eb
      rw [Nat.cast_succ, show ((k : ℝ) + 1) / (n : ℝ)
        = (k : ℝ) / (n : ℝ) + 1 / (n : ℝ) by ring, ← ea, ← eb]
      exact PCM.ovee_congr (ih hk') key0 ha' hb'
  have hfin := key n le_rfl
  rwa [div_self (ne_of_gt hn0), GP.Iv_one, WeightMod.one_smul,
    WeightMod.one_smul] at hfin

/-- **Divisibility**: `|a| ≤ l ≠ 0` implies `a = l • e` for some `e`. -/
theorem exists_smul_eq {l : I} (hl : l ≠ 0) {a : X} (ha : ((wt a : I) : ℝ) ≤ l) :
    ∃ e : X, l • e = a := by
  obtain ⟨n, c, hn1, hcl⟩ := GP.exists_nat_scale hl
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1n0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hcl' : (l : ℝ) * c = 1 / (n : ℝ) := by
    have := congrArg Subtype.val hcl
    rwa [GP.I_coe_mul, GP.Iv_coe h1n0 (by rw [div_le_one hn0]; exact hn1)] at this
  have hca : ((wt (c • a) : I) : ℝ) ≤ 1 / (n : ℝ) := by
    rw [WeightMod.wt_smul, GP.I_coe_mul, ← hcl', mul_comm (l : ℝ)]
    exact mul_le_mul_of_nonneg_left ha c.2.1
  have step : ∀ k : ℕ, (k : ℝ) ≤ (n : ℝ) →
      ∃ s : X, ((wt s : I) : ℝ) ≤ (k : ℝ) / (n : ℝ)
        ∧ l • s = GP.Iv ((k : ℝ) / (n : ℝ)) • a := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, by rw [WeightMod.wt_zero]; simp, ?_⟩
      rw [Nat.cast_zero, zero_div, GP.Iv_zero, WeightMod.zero_smul a, WeightMod.smul_zero l]
    | succ k ih =>
      intro hk
      rw [Nat.cast_succ] at hk
      have hk' : (k : ℝ) ≤ (n : ℝ) := by linarith
      obtain ⟨s, hsle, hseq⟩ := ih hk'
      have hkn0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
      have hsum : (k : ℝ) / (n : ℝ) + 1 / (n : ℝ) ≤ 1 := by
        rw [← add_div, div_le_one hn0]; linarith
      have hp := GP.Iv_perp hkn0 h1n0 hsum
      have hs' : Perp s (c • a) := WeightMod.perp_of_wt (by linarith)
      obtain ⟨hy, ey⟩ := WeightMod.perp_smul hp a
      rw [GP.Iv_ovee hkn0 h1n0 hsum hp] at ey
      rw [Nat.cast_succ, show ((k : ℝ) + 1) / (n : ℝ)
        = (k : ℝ) / (n : ℝ) + 1 / (n : ℝ) by ring]
      refine ⟨ovee s (c • a) hs', ?_, ?_⟩
      · rw [WeightMod.wt_ovee hs']; linarith
      · obtain ⟨hz, ez⟩ := WeightMod.smul_perp l hs'
        rw [← ez]
        have e1 : l • (c • a) = GP.Iv (1 / (n : ℝ)) • a := by
          rw [← WeightMod.mul_smul, hcl]
        rw [PCM.ovee_congr hseq e1 hz hy, ey]
  obtain ⟨s, _, hs⟩ := step n le_rfl
  refine ⟨s, ?_⟩
  rwa [div_self (ne_of_gt hn0), GP.Iv_one, WeightMod.one_smul] at hs

theorem frac_smul_frac {r q N : ℝ≥0} (h1 : r ≤ q) (h2 : q ≤ N) (a : X) :
    GP.frac q N • (GP.frac r q • a) = GP.frac r N • a := by
  rw [← WeightMod.mul_smul, GP.frac_mul h1 h2]

/-! ### The cone of a cancellative weight module -/

/-- `(r, a) ≈ (s, b)`: `r · a` and `s · b` agree at a common scale. -/
def coneRel (x y : ℝ≥0 × X) : Prop :=
  ∃ N : ℝ≥0, x.1 ≤ N ∧ y.1 ≤ N ∧ GP.frac x.1 N • x.2 = GP.frac y.1 N • y.2

theorem coneRel_at {x y : ℝ≥0 × X} (h : coneRel x y) {N : ℝ≥0}
    (hx : x.1 ≤ N) (hy : y.1 ≤ N) : GP.frac x.1 N • x.2 = GP.frac y.1 N • y.2 := by
  obtain ⟨M, hxM, hyM, hM⟩ := h
  have hMK : M ≤ max M N := le_max_left _ _
  have hNK : N ≤ max M N := le_max_right _ _
  have e1 : GP.frac x.1 (max M N) • x.2 = GP.frac y.1 (max M N) • y.2 := by
    rw [← frac_smul_frac hxM hMK, ← frac_smul_frac hyM hMK, hM]
  rcases eq_or_ne N 0 with hN0 | hN0
  · subst hN0
    have hx0 : x.1 = 0 := le_antisymm hx zero_le
    have hy0 : y.1 = 0 := le_antisymm hy zero_le
    rw [hx0, hy0, GP.frac_zero, WeightMod.zero_smul, WeightMod.zero_smul]
  · refine smul_left_cancel (GP.frac_ne_zero hN0 hNK) ?_
    rw [frac_smul_frac hx hNK, frac_smul_frac hy hNK]
    exact e1

theorem coneRel_refl (x : ℝ≥0 × X) : coneRel x x := ⟨x.1, le_rfl, le_rfl, rfl⟩

theorem coneRel_symm {x y : ℝ≥0 × X} (h : coneRel x y) : coneRel y x := by
  obtain ⟨N, hx, hy, e⟩ := h
  exact ⟨N, hy, hx, e.symm⟩

theorem coneRel_trans {x y z : ℝ≥0 × X} (h1 : coneRel x y) (h2 : coneRel y z) :
    coneRel x z := by
  refine ⟨max (max x.1 y.1) z.1, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_max_right _ _
  · refine (coneRel_at h1 ?_ ?_).trans (coneRel_at h2 ?_ ?_)
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_max_right _ _

variable (X) in
def coneSetoid : Setoid (ℝ≥0 × X) :=
  ⟨coneRel, coneRel_refl, fun h => coneRel_symm h, fun h1 h2 => coneRel_trans h1 h2⟩

variable (X) in
/-- The cone of formal multiples `r · a`. -/
def Cone : Type uw := Quotient (coneSetoid X)

def Cone.mk (r : ℝ≥0) (a : X) : Cone X := Quotient.mk (coneSetoid X) (r, a)

theorem Cone.mk_eq_mk {r s : ℝ≥0} {a b : X} :
    Cone.mk r a = Cone.mk s b ↔ coneRel (r, a) (s, b) :=
  Quotient.eq (r := coneSetoid X)

theorem Cone.ind {motive : Cone X → Prop} (h : ∀ (r : ℝ≥0) (a : X), motive (Cone.mk r a))
    (x : Cone X) : motive x :=
  Quotient.ind (fun p => h p.1 p.2) x

noncomputable def coneAddRaw (x y : ℝ≥0 × X) : ℝ≥0 × X :=
  (x.1 + y.1,
    ovee (GP.frac x.1 (x.1 + y.1) • x.2) (GP.frac y.1 (x.1 + y.1) • y.2)
      (smul_perp_smul (GP.frac_perp (le_refl (x.1 + y.1))) x.2 y.2))

theorem coneAddRaw_smul {r s N : ℝ≥0} (h : r + s ≤ N) (a b : X) :
    GP.frac (coneAddRaw (r, a) (s, b)).1 N • (coneAddRaw (r, a) (s, b)).2
      = ovee (GP.frac r N • a) (GP.frac s N • b)
          (smul_perp_smul (GP.frac_perp h) a b) := by
  obtain ⟨h', e⟩ := WeightMod.smul_perp (GP.frac (r + s) N)
    (smul_perp_smul (GP.frac_perp (le_refl (r + s))) a b)
  refine e.symm.trans (PCM.ovee_congr ?_ ?_ h' _)
  · exact frac_smul_frac (by simp) h a
  · exact frac_smul_frac (by simp) h b

theorem coneAddRaw_rel₂ {x x' y y' : ℝ≥0 × X} (hx : coneRel x x') (hy : coneRel y y') :
    coneRel (coneAddRaw x y) (coneAddRaw x' y') := by
  obtain ⟨r, a⟩ := x; obtain ⟨r', a'⟩ := x'
  obtain ⟨s, b⟩ := y; obtain ⟨s', b'⟩ := y'
  refine ⟨max r r' + max s s', ?_, ?_, ?_⟩
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)
  · rw [coneAddRaw_smul (add_le_add (le_max_left _ _) (le_max_left _ _)),
      coneAddRaw_smul (add_le_add (le_max_right _ _) (le_max_right _ _))]
    exact PCM.ovee_congr
      (coneRel_at hx (le_trans (le_max_left r r') le_self_add)
        (le_trans (le_max_right r r') le_self_add))
      (coneRel_at hy (le_trans (le_max_left s s') le_add_self)
        (le_trans (le_max_right s s') le_add_self)) _ _

theorem wt_frac_le {r N : ℝ≥0} (h : r ≤ N) (a : X) :
    ((wt (GP.frac r N • a) : I) : ℝ) ≤ (r : ℝ) / N := by
  have := wt_le_of_le (l := GP.frac r N) a
  rwa [GP.frac_coe h] at this

theorem perp_ovee_frac {r s q N : ℝ≥0} (h : r + s + q ≤ N) {a b c : X}
    (hab : Perp (GP.frac r N • a) (GP.frac s N • b)) :
    Perp (ovee (GP.frac r N • a) (GP.frac s N • b) hab) (GP.frac q N • c) := by
  rw [perp_iff_wt, WeightMod.wt_ovee]
  have hr : r ≤ N := le_trans (le_trans le_self_add le_self_add) h
  have hs : s ≤ N := le_trans (le_trans le_add_self le_self_add) h
  have hq : q ≤ N := le_trans le_add_self h
  have h1 := wt_frac_le hr a; have h2 := wt_frac_le hs b; have h3 := wt_frac_le hq c
  have : (r : ℝ) / N + s / N + q / N ≤ 1 := by
    rcases eq_or_ne N 0 with hN | hN
    · subst hN; simp
    · have hN' : (0 : ℝ) < N := by positivity
      rw [← add_div, ← add_div, div_le_one hN']; exact_mod_cast h
  linarith

theorem perp_frac_ovee {r s q N : ℝ≥0} (h : r + (s + q) ≤ N) {a b c : X}
    (hbc : Perp (GP.frac s N • b) (GP.frac q N • c)) :
    Perp (GP.frac r N • a) (ovee (GP.frac s N • b) (GP.frac q N • c) hbc) := by
  rw [perp_iff_wt, WeightMod.wt_ovee]
  have hr : r ≤ N := le_trans le_self_add h
  have hs : s ≤ N := le_trans (le_trans le_self_add le_add_self) h
  have hq : q ≤ N := le_trans (le_trans le_add_self le_add_self) h
  have h1 := wt_frac_le hr a; have h2 := wt_frac_le hs b; have h3 := wt_frac_le hq c
  have : (r : ℝ) / N + (s / N + q / N) ≤ 1 := by
    rcases eq_or_ne N 0 with hN | hN
    · subst hN; simp
    · have hN' : (0 : ℝ) < N := by positivity
      rw [← add_div, ← add_div, div_le_one hN']; exact_mod_cast h
  linarith

noncomputable instance : Add (Cone X) where
  add := Quotient.lift₂
    (fun p q => (Quotient.mk (coneSetoid X) (coneAddRaw p q) : Cone X))
    (fun _ _ _ _ h1 h2 => Quotient.sound (coneAddRaw_rel₂ h1 h2))

theorem Cone.mk_add (r s : ℝ≥0) (a b : X) :
    Cone.mk r a + Cone.mk s b
      = Quotient.mk (coneSetoid X) (coneAddRaw (r, a) (s, b)) := rfl

theorem Cone.eq_iff {r s N : ℝ≥0} {a b : X} (hr : r ≤ N) (hs : s ≤ N) :
    Cone.mk r a = Cone.mk s b ↔ GP.frac r N • a = GP.frac s N • b := by
  rw [Cone.mk_eq_mk]
  exact ⟨fun h => coneRel_at h hr hs, fun h => ⟨N, hr, hs, h⟩⟩

theorem Cone.mk_rescale {r N : ℝ≥0} (h : r ≤ N) (a : X) :
    Cone.mk r a = Cone.mk N (GP.frac r N • a) := by
  rw [Cone.eq_iff h (le_refl N)]
  rcases eq_or_ne N 0 with hN | hN
  · subst hN
    have hr : r = 0 := le_antisymm h zero_le
    subst hr
    rw [GP.frac_zero, WeightMod.zero_smul, WeightMod.zero_smul]
  · rw [GP.frac_self hN, WeightMod.one_smul]

theorem Cone.mk_inj {N : ℝ≥0} (hN : N ≠ 0) {a b : X} :
    Cone.mk N a = Cone.mk N b ↔ a = b := by
  rw [Cone.eq_iff (le_refl N) (le_refl N), GP.frac_self hN, WeightMod.one_smul,
    WeightMod.one_smul]

theorem Cone.add_same {N : ℝ≥0} {a b : X} (h : Perp a b) :
    Cone.mk N a + Cone.mk N b = Cone.mk N (ovee a b h) := by
  rw [Cone.mk_add, Cone.mk_rescale (show N ≤ N + N by simp) (ovee a b h)]
  show Quotient.mk (coneSetoid X) (coneAddRaw (N, a) (N, b)) = _
  obtain ⟨h', e⟩ := WeightMod.smul_perp (GP.frac N (N + N)) h
  refine congrArg (Quotient.mk (coneSetoid X)) (Prod.ext rfl ?_)
  show ovee (GP.frac N (N + N) • a) (GP.frac N (N + N) • b) _
      = GP.frac N (N + N) • ovee a b h
  exact e

theorem Cone.add_eq {r s N : ℝ≥0} {a b : X} (h : r + s ≤ N)
    (hp : Perp (GP.frac r N • a) (GP.frac s N • b)) :
    Cone.mk r a + Cone.mk s b = Cone.mk N (ovee (GP.frac r N • a) (GP.frac s N • b) hp) := by
  rw [Cone.mk_rescale (le_trans (by simp) h) a, Cone.mk_rescale (le_trans (by simp) h) b,
    Cone.add_same hp]

noncomputable instance : Zero (Cone X) := ⟨Cone.mk 0 0⟩

theorem Cone.zero_def : (0 : Cone X) = Cone.mk 0 0 := rfl

theorem Cone.mk_zero_scale (a : X) : Cone.mk 0 a = 0 := by
  rw [Cone.zero_def, Cone.eq_iff (le_refl (0 : ℝ≥0)) (le_refl (0 : ℝ≥0)),
    GP.frac_zero, WeightMod.zero_smul, WeightMod.zero_smul]

theorem Cone.mk_eq_of_scale_zero {N : ℝ≥0} (hN : N = 0) (a b : X) :
    Cone.mk N a = Cone.mk N b := by
  subst hN; rw [Cone.mk_zero_scale, Cone.mk_zero_scale]

theorem Cone.mk_zero (N : ℝ≥0) : Cone.mk N (0 : X) = 0 := by
  rw [Cone.zero_def, Cone.eq_iff (le_refl N) (zero_le), GP.frac_zero, WeightMod.smul_zero,
    WeightMod.zero_smul]

noncomputable instance : AddCommMonoid (Cone X) where
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  add_assoc := by
    refine Cone.ind (fun r a => Cone.ind (fun s b => Cone.ind (fun q c => ?_)))
    have hr : r ≤ r + s + q := le_trans le_self_add le_self_add
    have hs : s ≤ r + s + q := le_trans le_add_self le_self_add
    have hq : q ≤ r + s + q := le_add_self
    have hrs : r + s ≤ r + s + q := le_self_add
    have hsq : s + q ≤ r + s + q := by
      rw [show r + s + q = r + (s + q) by ring]; exact le_add_self
    have hA : Perp (GP.frac r (r + s + q) • a) (GP.frac s (r + s + q) • b) :=
      smul_perp_smul (GP.frac_perp hrs) a b
    have hBC : Perp (GP.frac s (r + s + q) • b) (GP.frac q (r + s + q) • c) :=
      smul_perp_smul (GP.frac_perp hsq) b c
    have hAB_C := perp_ovee_frac (le_refl (r + s + q)) hA (c := c)
    have hA_BC := perp_frac_ovee (by rw [show r + s + q = r + (s + q) by ring]) hBC (a := a)
    rw [Cone.mk_rescale hr a, Cone.mk_rescale hs b, Cone.mk_rescale hq c,
      Cone.add_same hA, Cone.add_same hAB_C, Cone.add_same hBC, Cone.add_same hA_BC]
    exact congrArg (Cone.mk (r + s + q)) (PCM.ovee_assoc hA hAB_C)
  zero_add := by
    refine Cone.ind (fun s b => ?_)
    rw [Cone.zero_def, Cone.mk_rescale (zero_le : (0 : ℝ≥0) ≤ s) (0 : X), GP.frac_zero,
      WeightMod.zero_smul, Cone.add_same (PCM.zero_perp b), PCM.zero_ovee]
  add_zero := by
    refine Cone.ind (fun s b => ?_)
    rw [Cone.zero_def, Cone.mk_rescale (zero_le : (0 : ℝ≥0) ≤ s) (0 : X), GP.frac_zero,
      WeightMod.zero_smul, Cone.add_same (PCM.perp_zero b), PCM.ovee_zero]
  add_comm := by
    refine Cone.ind (fun r a => Cone.ind (fun s b => ?_))
    have hr : r ≤ r + s := le_self_add
    have hs : s ≤ r + s := le_add_self
    rw [Cone.mk_rescale hr a, Cone.mk_rescale hs b,
      Cone.add_same (smul_perp_smul (GP.frac_perp (le_refl (r + s))) a b),
      Cone.add_same (smul_perp_smul (GP.frac_perp (le_of_eq (add_comm s r))) b a)]
    exact congrArg (Cone.mk (r + s)) (PCM.ovee_comm _)

theorem Cone.add_right_cancel (hX : WeightMod.Cancellative X) {x y z : Cone X}
    (h : x + z = y + z) : x = y := by
  revert h
  induction x using Cone.ind with
  | _ r a =>
  induction y using Cone.ind with
  | _ s b =>
  induction z using Cone.ind with
  | _ q c =>
    intro h
    have hr : r ≤ r + s + q := le_trans le_self_add le_self_add
    have hs : s ≤ r + s + q := le_trans le_add_self le_self_add
    have hq : q ≤ r + s + q := le_add_self
    have hrq : r + q ≤ r + s + q := by
      rw [show r + s + q = r + q + s by ring]; exact le_self_add
    have hsq : s + q ≤ r + s + q := by
      rw [show r + s + q = r + (s + q) by ring]; exact le_add_self
    rw [Cone.mk_rescale hr a, Cone.mk_rescale hs b, Cone.mk_rescale hq c] at h
    rw [Cone.mk_rescale hr a, Cone.mk_rescale hs b]
    rcases eq_or_ne (r + s + q) 0 with hN0 | hN0
    · rw [hN0, Cone.mk_zero_scale, Cone.mk_zero_scale]
    · have h1 := smul_perp_smul (GP.frac_perp hrq) a c
      have h2 := smul_perp_smul (GP.frac_perp hsq) b c
      rw [Cone.add_same h1, Cone.add_same h2, Cone.mk_inj hN0] at h
      rw [Cone.mk_inj hN0]
      rw [PCM.ovee_comm h1, PCM.ovee_comm h2] at h
      exact hX _ _ h

theorem Cone.eq_zero_of_add_eq_zero {p q : Cone X} (h : p + q = 0) : p = 0 := by
  revert h
  induction p using Cone.ind with
  | _ r a =>
  induction q using Cone.ind with
  | _ s b =>
    intro h
    have hr : r ≤ r + s := le_self_add
    rw [Cone.add_eq (le_refl (r + s)) (smul_perp_smul (GP.frac_perp (le_refl (r + s))) a b),
      Cone.zero_def, Cone.eq_iff (le_refl (r + s)) zero_le, GP.frac_zero,
      WeightMod.zero_smul] at h
    rcases eq_or_ne (r + s) 0 with hN0 | hN0
    · have hr0 : r = 0 := le_antisymm (by rw [← hN0]; exact hr) zero_le
      rw [hr0, Cone.mk_zero_scale]
    · rw [GP.frac_self hN0, WeightMod.one_smul] at h
      have hw := congrArg (fun x : X => ((wt x : I) : ℝ)) h
      rw [WeightMod.wt_ovee, WeightMod.wt_zero, GP.I_coe_zero] at hw
      have h0 : GP.frac r (r + s) • a = 0 := by
        refine WeightMod.eq_zero_of_wt _ (Subtype.ext ?_)
        have := (wt (GP.frac s (r + s) • b)).2.1
        have := (wt (GP.frac r (r + s) • a)).2.1
        show ((wt (GP.frac r (r + s) • a) : I) : ℝ) = 0
        linarith
      rw [Cone.zero_def, Cone.eq_iff hr zero_le, GP.frac_zero, WeightMod.zero_smul, h0]

noncomputable def coneSmulRaw (t : ℝ≥0) (x : ℝ≥0 × X) : ℝ≥0 × X := (t * x.1, x.2)

theorem coneSmulRaw_rel (t : ℝ≥0) {x y : ℝ≥0 × X} (h : coneRel x y) :
    coneRel (coneSmulRaw t x) (coneSmulRaw t y) := by
  obtain ⟨N, hx, hy, e⟩ := h
  refine ⟨t * N, mul_le_mul_of_nonneg_left hx zero_le,
    mul_le_mul_of_nonneg_left hy zero_le, ?_⟩
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    show GP.frac (0 * _) (0 * N) • _ = GP.frac (0 * _) (0 * N) • _
    rw [zero_mul, zero_mul, zero_mul, GP.frac_zero, WeightMod.zero_smul, WeightMod.zero_smul]
  · show GP.frac (t * _) (t * N) • _ = GP.frac (t * _) (t * N) • _
    rw [GP.frac_mul_left ht, GP.frac_mul_left ht]
    exact e

noncomputable instance : SMul ℝ≥0 (Cone X) where
  smul t := Quotient.lift
    (fun x => (Quotient.mk (coneSetoid X) (coneSmulRaw t x) : Cone X))
    (fun _ _ h => Quotient.sound (coneSmulRaw_rel t h))

theorem Cone.smul_mk (t r : ℝ≥0) (a : X) : t • Cone.mk r a = Cone.mk (t * r) a := rfl

theorem Cone.one_smul (x : Cone X) : (1 : ℝ≥0) • x = x := by
  induction x using Cone.ind with
  | _ r a => rw [Cone.smul_mk, one_mul]

theorem Cone.zero_smul (x : Cone X) : (0 : ℝ≥0) • x = 0 := by
  induction x using Cone.ind with
  | _ r a => rw [Cone.smul_mk, zero_mul, Cone.mk_zero_scale]

theorem Cone.smul_zero (t : ℝ≥0) : t • (0 : Cone X) = 0 := by
  rw [Cone.zero_def, Cone.smul_mk, mul_zero, Cone.mk_zero_scale]

theorem Cone.mul_smul (t t' : ℝ≥0) (x : Cone X) : (t * t') • x = t • t' • x := by
  induction x using Cone.ind with
  | _ r a => rw [Cone.smul_mk, Cone.smul_mk, Cone.smul_mk, mul_assoc]

theorem Cone.smul_add (t : ℝ≥0) (x y : Cone X) : t • (x + y) = t • x + t • y := by
  induction x using Cone.ind with
  | _ r a =>
  induction y using Cone.ind with
  | _ s b =>
    have hp : Perp (GP.frac r (r + s) • a) (GP.frac s (r + s) • b) :=
      smul_perp_smul (GP.frac_perp (le_refl (r + s))) a b
    rw [Cone.add_eq (le_refl (r + s)) hp, Cone.smul_mk, Cone.smul_mk, Cone.smul_mk]
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [zero_mul, zero_mul, zero_mul, Cone.mk_zero_scale, Cone.mk_zero_scale,
        Cone.mk_zero_scale, add_zero]
    · have hle : t * r + t * s ≤ t * (r + s) := le_of_eq (by ring)
      have hp' : Perp (GP.frac (t * r) (t * (r + s)) • a) (GP.frac (t * s) (t * (r + s)) • b) :=
        smul_perp_smul (GP.frac_perp hle) a b
      rw [Cone.add_eq hle hp']
      exact congrArg (Cone.mk (t * (r + s)))
        (PCM.ovee_congr (by rw [GP.frac_mul_left ht]) (by rw [GP.frac_mul_left ht]) hp hp')

theorem Cone.add_smul (t t' : ℝ≥0) (x : Cone X) : (t + t') • x = t • x + t' • x := by
  induction x using Cone.ind with
  | _ r a =>
    rw [Cone.smul_mk, Cone.smul_mk, Cone.smul_mk]
    have hle : t * r + t' * r ≤ (t + t') * r := le_of_eq (by ring)
    have hp : Perp (GP.frac (t * r) ((t + t') * r) • a) (GP.frac (t' * r) ((t + t') * r) • a) :=
      smul_perp_smul (GP.frac_perp hle) a a
    rw [Cone.add_eq hle hp]
    rcases eq_or_ne ((t + t') * r) 0 with hN | hN
    · exact Cone.mk_eq_of_scale_zero hN _ _
    · have hfp : Perp (GP.frac (t * r) ((t + t') * r)) (GP.frac (t' * r) ((t + t') * r)) :=
        GP.frac_perp hle
      obtain ⟨hp2, e2⟩ := WeightMod.perp_smul hfp a
      rw [GP.frac_ovee hle] at e2
      rw [show t * r + t' * r = (t + t') * r by ring, GP.frac_self hN,
        WeightMod.one_smul] at e2
      exact congrArg (Cone.mk ((t + t') * r)) e2.symm

/-- The trace on the cone: `τ(r · a) = r |a|`. -/
theorem coneTr_rel {x y : ℝ≥0 × X} (h : coneRel x y) :
    (x.1 : ℝ) * (wt x.2 : ℝ) = (y.1 : ℝ) * (wt y.2 : ℝ) := by
  obtain ⟨N, hx, hy, e⟩ := h
  have := congrArg (fun z : X => ((wt z : I) : ℝ)) e
  simp only [WeightMod.wt_smul, GP.I_coe_mul, GP.frac_coe hx, GP.frac_coe hy] at this
  rcases eq_or_ne N 0 with hN | hN
  · subst hN
    rw [le_antisymm hx zero_le, le_antisymm hy zero_le]; simp
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp at this
    linarith

noncomputable def Cone.tr : Cone X → ℝ :=
  Quotient.lift (fun x : ℝ≥0 × X => (x.1 : ℝ) * (wt x.2 : ℝ)) (fun _ _ h => coneTr_rel h)

theorem Cone.tr_mk (r : ℝ≥0) (a : X) : Cone.tr (Cone.mk r a) = (r : ℝ) * (wt a : ℝ) := rfl

theorem Cone.tr_nonneg (p : Cone X) : 0 ≤ Cone.tr p := by
  induction p using Cone.ind with
  | _ r a => rw [Cone.tr_mk]; exact mul_nonneg r.2 (wt a).2.1

theorem Cone.tr_add (p q : Cone X) : Cone.tr (p + q) = Cone.tr p + Cone.tr q := by
  induction p using Cone.ind with
  | _ r a =>
  induction q using Cone.ind with
  | _ s b =>
    have hp : Perp (GP.frac r (r + s) • a) (GP.frac s (r + s) • b) :=
      smul_perp_smul (GP.frac_perp (le_refl (r + s))) a b
    rw [Cone.add_eq (le_refl _) hp, Cone.tr_mk, Cone.tr_mk, Cone.tr_mk, WeightMod.wt_ovee,
      WeightMod.wt_smul, WeightMod.wt_smul, GP.I_coe_mul, GP.I_coe_mul,
      GP.frac_coe (le_self_add : r ≤ r + s), GP.frac_coe (le_add_self : s ≤ r + s)]
    rcases eq_or_ne (r + s) 0 with hN | hN
    · have hr : r = 0 := le_antisymm (hN ▸ le_self_add) zero_le
      have hs : s = 0 := le_antisymm (hN ▸ le_add_self) zero_le
      subst hr; subst hs; simp
    · have hN' : ((r + s : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast hN
      push_cast at hN' ⊢
      field_simp

theorem Cone.tr_smul (t : ℝ≥0) (p : Cone X) : Cone.tr (t • p) = t * Cone.tr p := by
  induction p using Cone.ind with
  | _ r a => rw [Cone.smul_mk, Cone.tr_mk, Cone.tr_mk]; push_cast; ring

theorem Cone.eq_zero_of_tr (p : Cone X) (h : Cone.tr p = 0) : p = 0 := by
  induction p using Cone.ind with
  | _ r a =>
    rw [Cone.tr_mk] at h
    rcases mul_eq_zero.1 h with h | h
    · have : r = 0 := by exact_mod_cast h
      rw [this, Cone.mk_zero_scale]
    · rw [WeightMod.eq_zero_of_wt a (Subtype.ext h), Cone.mk_zero]

section Vec

variable {X : Type uw} [PCM X] [WeightMod X] [hX : Fact (WeightMod.Cancellative X)]

/-- `(p, q)` stands for `p - q`. -/
def vRel (x y : Cone X × Cone X) : Prop := x.1 + y.2 = y.1 + x.2

theorem vRel_trans {x y z : Cone X × Cone X} (h1 : vRel x y) (h2 : vRel y z) :
    vRel x z := by
  refine Cone.add_right_cancel hX.out (z := y.1 + y.2) ?_
  calc x.1 + z.2 + (y.1 + y.2) = (x.1 + y.2) + (y.1 + z.2) := by abel
    _ = (y.1 + x.2) + (z.1 + y.2) := by rw [h1, h2]
    _ = z.1 + x.2 + (y.1 + y.2) := by abel

variable (X) in
/-- The setoid of formal differences. -/
def vSetoid : Setoid (Cone X × Cone X) :=
  ⟨vRel, fun _ => rfl, fun h => h.symm, fun h1 h2 => vRel_trans h1 h2⟩

variable (X) in
/-- The **representing vector space**: formal differences of cone elements. -/
def Vec : Type uw := Quotient (vSetoid X)

/-- The class of `p - q`. -/
def Vec.mk (p q : Cone X) : Vec X := Quotient.mk (vSetoid X) (p, q)

theorem Vec.mk_eq {p q p' q' : Cone X} :
    Vec.mk p q = Vec.mk p' q' ↔ p + q' = p' + q :=
  Quotient.eq (r := vSetoid X)

theorem Vec.ind {motive : Vec X → Prop} (h : ∀ p q : Cone X, motive (Vec.mk p q))
    (x : Vec X) : motive x :=
  Quotient.ind (fun p => h p.1 p.2) x

noncomputable instance : Add (Vec X) where
  add := Quotient.lift₂ (fun x y => Vec.mk (x.1 + y.1) (x.2 + y.2))
    (by
      rintro ⟨p, q⟩ ⟨p', q'⟩ ⟨r, t⟩ ⟨r', t'⟩ h1 h2
      refine Quotient.sound ?_
      show p + p' + (t + t') = r + r' + (q + q')
      calc p + p' + (t + t') = (p + t) + (p' + t') := by abel
        _ = (r + q) + (r' + q') := by rw [show p + t = r + q from h1,
              show p' + t' = r' + q' from h2]
        _ = r + r' + (q + q') := by abel)

theorem Vec.mk_add (p q p' q' : Cone X) :
    Vec.mk p q + Vec.mk p' q' = Vec.mk (p + p') (q + q') := rfl

noncomputable instance : Neg (Vec X) where
  neg := Quotient.lift (fun x => Vec.mk x.2 x.1)
    (by
      rintro ⟨p, q⟩ ⟨p', q'⟩ h
      refine Quotient.sound ?_
      show q + p' = q' + p
      have : p + q' = p' + q := h
      rw [add_comm q p', ← this, add_comm])

theorem Vec.mk_neg (p q : Cone X) : -Vec.mk p q = Vec.mk q p := rfl

noncomputable instance : Zero (Vec X) := ⟨Vec.mk 0 0⟩

theorem Vec.zero_def : (0 : Vec X) = Vec.mk 0 0 := rfl

noncomputable instance : AddCommGroup (Vec X) where
  add_assoc := by
    refine Vec.ind (fun p q => Vec.ind (fun p' q' => Vec.ind (fun p'' q'' => ?_)))
    rw [Vec.mk_add, Vec.mk_add, Vec.mk_add, Vec.mk_add, add_assoc, add_assoc]
  zero_add := by
    refine Vec.ind (fun p q => ?_)
    rw [Vec.zero_def, Vec.mk_add, zero_add, zero_add]
  add_zero := by
    refine Vec.ind (fun p q => ?_)
    rw [Vec.zero_def, Vec.mk_add, add_zero, add_zero]
  add_comm := by
    refine Vec.ind (fun p q => Vec.ind (fun p' q' => ?_))
    rw [Vec.mk_add, Vec.mk_add, add_comm p p', add_comm q q']
  neg_add_cancel := by
    refine Vec.ind (fun p q => ?_)
    rw [Vec.mk_neg, Vec.mk_add, Vec.zero_def, Vec.mk_eq]
    abel
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-! ### `Vec X` is a real vector space -/

noncomputable instance : SMul ℝ≥0 (Vec X) where
  smul t := Quotient.lift (fun x : Cone X × Cone X => Vec.mk (t • x.1) (t • x.2))
    (by
      rintro ⟨p, q⟩ ⟨p', q'⟩ h
      refine Quotient.sound ?_
      show t • p + t • q' = t • p' + t • q
      rw [← Cone.smul_add, ← Cone.smul_add, show p + q' = p' + q from h])

theorem Vec.nnsmul_mk (t : ℝ≥0) (p q : Cone X) :
    t • Vec.mk p q = Vec.mk (t • p) (t • q) := rfl

theorem Vec.nnsmul_add (t : ℝ≥0) (x y : Vec X) : t • (x + y) = t • x + t • y := by
  induction x using Vec.ind with
  | _ p q =>
  induction y using Vec.ind with
  | _ p' q' =>
    rw [Vec.mk_add, Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.mk_add,
      Cone.smul_add, Cone.smul_add]

theorem Vec.add_nnsmul (t t' : ℝ≥0) (x : Vec X) : (t + t') • x = t • x + t' • x := by
  induction x using Vec.ind with
  | _ p q =>
    rw [Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.mk_add, Cone.add_smul,
      Cone.add_smul]

theorem Vec.nnsmul_nnsmul (t t' : ℝ≥0) (x : Vec X) : (t * t') • x = t • t' • x := by
  induction x using Vec.ind with
  | _ p q =>
    rw [Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.nnsmul_mk, Cone.mul_smul, Cone.mul_smul]

theorem Vec.one_nnsmul (x : Vec X) : (1 : ℝ≥0) • x = x := by
  induction x using Vec.ind with
  | _ p q => rw [Vec.nnsmul_mk, Cone.one_smul, Cone.one_smul]

theorem Vec.zero_nnsmul (x : Vec X) : (0 : ℝ≥0) • x = 0 := by
  induction x using Vec.ind with
  | _ p q => rw [Vec.nnsmul_mk, Cone.zero_smul, Cone.zero_smul, Vec.zero_def]

theorem Vec.nnsmul_zero (t : ℝ≥0) : t • (0 : Vec X) = 0 := by
  rw [Vec.zero_def, Vec.nnsmul_mk, Cone.smul_zero]

theorem Vec.nnsmul_neg (t : ℝ≥0) (x : Vec X) : t • (-x) = -(t • x) := by
  induction x using Vec.ind with
  | _ p q => rw [Vec.mk_neg, Vec.nnsmul_mk, Vec.nnsmul_mk, Vec.mk_neg]

theorem Vec.nnsmul_sub (t : ℝ≥0) (x y : Vec X) : t • (x - y) = t • x - t • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Vec.nnsmul_add, Vec.nnsmul_neg]

/-- The positive and negative parts of a real, as nonnegative scalars. -/
theorem toNNReal_key_add (t s : ℝ) :
    Real.toNNReal (t + s) + Real.toNNReal (-t) + Real.toNNReal (-s)
      = Real.toNNReal (-(t + s)) + Real.toNNReal t + Real.toNNReal s := by
  have hmax : ∀ x : ℝ, max x 0 = (x + |x|) / 2 := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
  refine NNReal.coe_injective ?_
  push_cast
  simp only [Real.coe_toNNReal', hmax, abs_neg]
  ring

theorem toNNReal_key_mul (t s : ℝ) :
    Real.toNNReal (t * s) + Real.toNNReal t * Real.toNNReal (-s)
        + Real.toNNReal (-t) * Real.toNNReal s
      = Real.toNNReal (-(t * s)) + Real.toNNReal t * Real.toNNReal s
        + Real.toNNReal (-t) * Real.toNNReal (-s) := by
  have hmax : ∀ x : ℝ, max x 0 = (x + |x|) / 2 := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
  refine NNReal.coe_injective ?_
  push_cast
  simp only [Real.coe_toNNReal', hmax, abs_neg, abs_mul]
  ring

noncomputable instance : SMul ℝ (Vec X) where
  smul t x := Real.toNNReal t • x - Real.toNNReal (-t) • x

theorem Vec.rsmul_def (t : ℝ) (x : Vec X) :
    t • x = Real.toNNReal t • x - Real.toNNReal (-t) • x := rfl

theorem Vec.rsmul_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Vec X) :
    t • x = Real.toNNReal t • x := by
  have h : Real.toNNReal (-t) = 0 := Real.toNNReal_of_nonpos (by linarith)
  rw [Vec.rsmul_def, h, Vec.zero_nnsmul, sub_zero]

noncomputable instance : Module ℝ (Vec X) where
  one_smul x := by
    rw [Vec.rsmul_nonneg zero_le_one, Real.toNNReal_one, Vec.one_nnsmul]
  mul_smul t s x := by
    have key : (Real.toNNReal (t * s) + Real.toNNReal t * Real.toNNReal (-s)
          + Real.toNNReal (-t) * Real.toNNReal s) • x
        = (Real.toNNReal (-(t * s)) + Real.toNNReal t * Real.toNNReal s
          + Real.toNNReal (-t) * Real.toNNReal (-s)) • x :=
      congrArg (fun c : ℝ≥0 => c • x) (toNNReal_key_mul t s)
    rw [Vec.add_nnsmul, Vec.add_nnsmul, Vec.add_nnsmul, Vec.add_nnsmul,
      Vec.nnsmul_nnsmul, Vec.nnsmul_nnsmul, Vec.nnsmul_nnsmul, Vec.nnsmul_nnsmul] at key
    show Real.toNNReal (t * s) • x - Real.toNNReal (-(t * s)) • x
      = Real.toNNReal t • (Real.toNNReal s • x - Real.toNNReal (-s) • x)
        - Real.toNNReal (-t) • (Real.toNNReal s • x - Real.toNNReal (-s) • x)
    rw [Vec.nnsmul_sub, Vec.nnsmul_sub]
    refine eq_of_sub_eq_zero ?_
    rw [show Real.toNNReal (t * s) • x - Real.toNNReal (-(t * s)) • x
        - (Real.toNNReal t • Real.toNNReal s • x - Real.toNNReal t • Real.toNNReal (-s) • x
          - (Real.toNNReal (-t) • Real.toNNReal s • x
            - Real.toNNReal (-t) • Real.toNNReal (-s) • x))
      = (Real.toNNReal (t * s) • x + Real.toNNReal t • Real.toNNReal (-s) • x
          + Real.toNNReal (-t) • Real.toNNReal s • x)
        - (Real.toNNReal (-(t * s)) • x + Real.toNNReal t • Real.toNNReal s • x
          + Real.toNNReal (-t) • Real.toNNReal (-s) • x) from by abel, key, sub_self]
  smul_zero t := by
    rw [Vec.rsmul_def, Vec.nnsmul_zero, Vec.nnsmul_zero, sub_zero]
  smul_add t x y := by
    rw [Vec.rsmul_def, Vec.rsmul_def, Vec.rsmul_def, Vec.nnsmul_add, Vec.nnsmul_add]
    abel
  add_smul t s x := by
    have key : (Real.toNNReal (t + s) + Real.toNNReal (-t) + Real.toNNReal (-s)) • x
        = (Real.toNNReal (-(t + s)) + Real.toNNReal t + Real.toNNReal s) • x :=
      congrArg (fun c : ℝ≥0 => c • x) (toNNReal_key_add t s)
    rw [Vec.add_nnsmul, Vec.add_nnsmul, Vec.add_nnsmul, Vec.add_nnsmul] at key
    show Real.toNNReal (t + s) • x - Real.toNNReal (-(t + s)) • x
      = (Real.toNNReal t • x - Real.toNNReal (-t) • x)
        + (Real.toNNReal s • x - Real.toNNReal (-s) • x)
    refine eq_of_sub_eq_zero ?_
    rw [show Real.toNNReal (t + s) • x - Real.toNNReal (-(t + s)) • x
        - ((Real.toNNReal t • x - Real.toNNReal (-t) • x)
          + (Real.toNNReal s • x - Real.toNNReal (-s) • x))
      = (Real.toNNReal (t + s) • x + Real.toNNReal (-t) • x + Real.toNNReal (-s) • x)
        - (Real.toNNReal (-(t + s)) • x + Real.toNNReal t • x + Real.toNNReal s • x)
      from by abel, key, sub_self]
  zero_smul x := by
    rw [Vec.rsmul_nonneg le_rfl, Real.toNNReal_zero, Vec.zero_nnsmul]

/-! ### The order -/

/-- The image of the cone in `Vec X`. -/
noncomputable def Vec.pos (p : Cone X) : Vec X := Vec.mk p 0

theorem Vec.pos_add (p q : Cone X) : Vec.pos (p + q) = Vec.pos p + Vec.pos q := by
  rw [Vec.pos, Vec.pos, Vec.pos, Vec.mk_add, add_zero]

theorem Vec.pos_zero : Vec.pos (0 : Cone X) = 0 := rfl

theorem Vec.pos_inj {p q : Cone X} : Vec.pos p = Vec.pos q ↔ p = q := by
  rw [Vec.pos, Vec.pos, Vec.mk_eq, add_zero, add_zero]

theorem Vec.pos_nnsmul (t : ℝ≥0) (p : Cone X) : t • Vec.pos p = Vec.pos (t • p) := by
  rw [Vec.pos, Vec.pos, Vec.nnsmul_mk, Cone.smul_zero]

theorem Vec.pos_rsmul {t : ℝ} (ht : 0 ≤ t) (p : Cone X) :
    t • Vec.pos p = Vec.pos (Real.toNNReal t • p) := by
  rw [Vec.rsmul_nonneg ht, Vec.pos_nnsmul]

theorem Vec.mk_eq_sub (p q : Cone X) : Vec.mk p q = Vec.pos p - Vec.pos q := by
  rw [sub_eq_add_neg, Vec.pos, Vec.pos, Vec.mk_neg, Vec.mk_add, zero_add, add_zero]

noncomputable instance : PartialOrder (Vec X) where
  le x y := ∃ p : Cone X, y = x + Vec.pos p
  le_refl x := ⟨0, by rw [Vec.pos_zero, add_zero]⟩
  le_trans x y z := by
    rintro ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by rw [Vec.pos_add, add_assoc]⟩
  le_antisymm x y := by
    rintro ⟨p, rfl⟩ ⟨q, hq⟩
    rw [add_assoc, ← Vec.pos_add] at hq
    have h0 : Vec.pos (p + q) = 0 :=
      add_left_cancel (a := x) (by rw [add_zero]; exact hq.symm)
    rw [← Vec.pos_zero, Vec.pos_inj] at h0
    rw [Cone.eq_zero_of_add_eq_zero h0, Vec.pos_zero, add_zero]

theorem Vec.le_def {x y : Vec X} : x ≤ y ↔ ∃ p : Cone X, y = x + Vec.pos p := Iff.rfl

theorem Vec.zero_le_pos (p : Cone X) : 0 ≤ Vec.pos p := ⟨p, by rw [zero_add]⟩

theorem Vec.exists_of_zero_le {x : Vec X} (h : 0 ≤ x) : ∃ p : Cone X, x = Vec.pos p := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, by rw [hp, zero_add]⟩

noncomputable instance : IsOrderedAddMonoid (Vec X) where
  add_le_add_left := by
    rintro x y ⟨p, rfl⟩ z
    exact ⟨p, by abel⟩
  add_le_add_right := by
    rintro x y ⟨p, rfl⟩ z
    exact ⟨p, by abel⟩

noncomputable instance : PosSMulMono ℝ (Vec X) where
  smul_le_smul_of_nonneg_left := by
    rintro c hc x y ⟨p, rfl⟩
    refine ⟨Real.toNNReal c • p, ?_⟩
    rw [smul_add, Vec.pos_rsmul hc]

noncomputable instance : SMulPosMono ℝ (Vec X) where
  smul_le_smul_of_nonneg_right := by
    rintro x hx c d hcd
    obtain ⟨p, rfl⟩ := Vec.exists_of_zero_le hx
    refine ⟨Real.toNNReal (d - c) • p, ?_⟩
    rw [← Vec.pos_rsmul (show (0:ℝ) ≤ d - c by linarith) p, ← add_smul,
      show c + (d - c) = d by ring]

end Vec

/-! ### The trace and the representation -/

section Repr

variable {X : Type uw} [PCM X] [WeightMod X] [hX : Fact (WeightMod.Cancellative X)]

theorem Cone.exists_mk (p : Cone X) : ∃ (r : ℝ≥0) (a : X), p = Cone.mk r a := by
  induction p using Cone.ind with
  | _ r a => exact ⟨r, a, rfl⟩

/-- The trace `τ(p - q) = τ p - τ q`. -/
noncomputable def Vec.trF : Vec X → ℝ :=
  Quotient.lift (fun x : Cone X × Cone X => Cone.tr x.1 - Cone.tr x.2) (by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    have h' : p + q' = p' + q := h
    have := congrArg Cone.tr h'
    rw [Cone.tr_add, Cone.tr_add] at this
    show Cone.tr p - Cone.tr q = Cone.tr p' - Cone.tr q'
    linarith)

theorem Vec.trF_mk (p q : Cone X) : Vec.trF (Vec.mk p q) = Cone.tr p - Cone.tr q := rfl

theorem Vec.trF_add (x y : Vec X) : Vec.trF (x + y) = Vec.trF x + Vec.trF y := by
  induction x using Vec.ind with
  | _ p q =>
  induction y using Vec.ind with
  | _ p' q' =>
    rw [Vec.mk_add, Vec.trF_mk, Vec.trF_mk, Vec.trF_mk, Cone.tr_add, Cone.tr_add]; ring

theorem Vec.trF_nnsmul (t : ℝ≥0) (x : Vec X) : Vec.trF (t • x) = t * Vec.trF x := by
  induction x using Vec.ind with
  | _ p q => rw [Vec.nnsmul_mk, Vec.trF_mk, Vec.trF_mk, Cone.tr_smul, Cone.tr_smul]; ring

theorem Vec.trF_neg (x : Vec X) : Vec.trF (-x) = -Vec.trF x := by
  induction x using Vec.ind with
  | _ p q => rw [Vec.mk_neg, Vec.trF_mk, Vec.trF_mk]; ring

/-- The trace of `Vec X`, a linear functional. -/
noncomputable def Vec.tr : Vec X →ₗ[ℝ] ℝ where
  toFun := Vec.trF
  map_add' := Vec.trF_add
  map_smul' t x := by
    show Vec.trF (Real.toNNReal t • x - Real.toNNReal (-t) • x) = t * Vec.trF x
    rw [sub_eq_add_neg, Vec.trF_add, Vec.trF_neg, Vec.trF_nnsmul, Vec.trF_nnsmul,
      Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith)]; ring

theorem Vec.tr_pos' (p : Cone X) : Vec.tr (Vec.pos p) = Cone.tr p := by
  show Vec.trF (Vec.mk p 0) = _
  rw [Vec.trF_mk, Cone.zero_def, Cone.tr_mk]; simp

theorem Vec.tr_nonneg {x : Vec X} (h : 0 ≤ x) : 0 ≤ Vec.tr x := by
  obtain ⟨p, rfl⟩ := Vec.exists_of_zero_le h
  rw [Vec.tr_pos']; exact Cone.tr_nonneg p

/-- The trace is strictly positive. -/
theorem Vec.tr_pos {x : Vec X} (h : 0 < x) : 0 < Vec.tr x := by
  obtain ⟨p, rfl⟩ := Vec.exists_of_zero_le h.le
  rcases (Vec.tr_nonneg h.le).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    rw [Vec.tr_pos'] at h'
    rw [Cone.eq_zero_of_tr p h'.symm, Vec.pos_zero] at h
    exact lt_irrefl _ h

/-- `Vec X` is positively generated. -/
theorem Vec.gen (x : Vec X) : ∃ a b : Vec X, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b := by
  induction x using Vec.ind with
  | _ p q => exact ⟨Vec.pos p, Vec.pos q, Vec.zero_le_pos p, Vec.zero_le_pos q,
      Vec.mk_eq_sub p q⟩

/-- The embedding `a ↦ 1 · a`. -/
noncomputable def gmap (a : X) : Vec X := Vec.pos (Cone.mk 1 a)

theorem gmap_ovee {a b : X} (h : Perp a b) : gmap (ovee a b h) = gmap a + gmap b := by
  rw [gmap, gmap, gmap, ← Vec.pos_add, Cone.add_same h]

theorem gmap_zero : gmap (0 : X) = 0 := by rw [gmap, Cone.mk_zero, Vec.pos_zero]

theorem gmap_injective : Function.Injective (gmap : X → Vec X) := by
  intro a b h
  rwa [gmap, gmap, Vec.pos_inj, Cone.mk_inj one_ne_zero] at h

theorem gmap_smul (l : I) (a : X) : gmap (l • a) = (l : ℝ) • gmap a := by
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := l.2.1
  have hle : Real.toNNReal (l : ℝ) ≤ 1 := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hl0, NNReal.coe_one]
    exact l.2.2
  rw [gmap, gmap, Vec.pos_rsmul hl0, Cone.smul_mk, mul_one]
  refine congrArg Vec.pos ?_
  rw [Cone.eq_iff (le_refl (1 : ℝ≥0)) hle, GP.frac_self one_ne_zero, WeightMod.one_smul,
    GP.frac_one, GP.Iv_congr (Real.coe_toNNReal _ hl0), GP.Iv_self]

theorem gmap_nonneg (a : X) : 0 ≤ gmap a := Vec.zero_le_pos _

theorem tr_gmap (a : X) : Vec.tr (gmap a) = (wt a : ℝ) := by
  rw [gmap, Vec.tr_pos', Cone.tr_mk]; simp

/-- The image of `gmap` is the whole subbase. -/
theorem gmap_surjective {x : Vec X} (h0 : 0 ≤ x) (h1 : Vec.tr x ≤ 1) : ∃ a : X, gmap a = x := by
  obtain ⟨p, rfl⟩ := Vec.exists_of_zero_le h0
  obtain ⟨r, a, rfl⟩ := Cone.exists_mk p
  rw [Vec.tr_pos', Cone.tr_mk] at h1
  rcases le_total r 1 with hr | hr
  · exact ⟨GP.frac r 1 • a, by rw [gmap, ← Cone.mk_rescale hr]⟩
  · have hr0 : (0 : ℝ) < r := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hne : GP.frac 1 r ≠ 0 := GP.frac_ne_zero one_ne_zero hr
    have hwa : ((wt a : I) : ℝ) ≤ (GP.frac 1 r : ℝ) := by
      rw [GP.frac_coe hr, le_div_iff₀ hr0]; push_cast; linarith
    obtain ⟨e, he⟩ := exists_smul_eq hne hwa
    refine ⟨e, ?_⟩
    rw [gmap, Cone.mk_rescale hr e, he]

theorem gmap_perp_iff {a b : X} :
    Perp a b ↔ Vec.tr (gmap a) + Vec.tr (gmap b) ≤ 1 := by
  rw [tr_gmap, tr_gmap, perp_iff_wt]

end Repr

end CW


/-! ## SIG 57: ordered vector spaces with trace, subbases, `CWMod` -/

/-- **SIG 57** (main.tex:1569, Definition): an **ordered vector space with
trace**: an ordered real vector space `V` (translation-invariant order, cone
closed under non-negative scalars) that is positively generated
(`V = V₊ - V₊`), with a linear functional `τ` (the trace) that is strictly
positive (`x > 0` implies `τ x > 0`). -/
structure OVSt : Type 1 where
  carrier : Type
  [grp : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [ord : PartialOrder carrier]
  [oam : IsOrderedAddMonoid carrier]
  [psm : PosSMulMono ℝ carrier]
  gen : ∀ x : carrier, ∃ a b : carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b
  tr : carrier →ₗ[ℝ] ℝ
  tr_pos : ∀ x : carrier, 0 < x → 0 < tr x

attribute [instance] OVSt.grp OVSt.mod OVSt.ord OVSt.oam OVSt.psm

namespace OVSt

theorem tr_nonneg (V : OVSt) {x : V.carrier} (h : 0 ≤ x) : 0 ≤ V.tr x := by
  rcases h.lt_or_eq with h | h
  · exact (V.tr_pos x h).le
  · rw [← h, map_zero]

/-- **SIG 57** (main.tex:1584, Definition): a morphism of `OVSt`: a
trace-decreasing positive linear map. -/
@[ext]
structure Hom (V W : OVSt) where
  toLin : V.carrier →ₗ[ℝ] W.carrier
  pos : ∀ x, 0 ≤ x → 0 ≤ toLin x
  tr_le : ∀ x, 0 ≤ x → W.tr (toLin x) ≤ V.tr x

/-- **SIG 57** (main.tex:1587, Definition): the category `OVSt`. -/
instance : Category OVSt where
  Hom := Hom
  id V := ⟨LinearMap.id, fun _ h => h, fun _ _ => le_rfl⟩
  comp f g := ⟨g.toLin ∘ₗ f.toLin, fun x h => g.pos _ (f.pos x h),
    fun x h => (g.tr_le _ (f.pos x h)).trans (f.tr_le x h)⟩

@[simp] theorem id_toLin (V : OVSt) : (𝟙 V : Hom V V).toLin = LinearMap.id := rfl
@[simp] theorem comp_toLin {U V W : OVSt} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).toLin = g.toLin ∘ₗ f.toLin := rfl

theorem hom_ext {V W : OVSt} {f g : V ⟶ W} (h : ∀ x, f.toLin x = g.toLin x) : f = g :=
  Hom.ext (LinearMap.ext h)

end OVSt

/-- **SIG 57** (main.tex:1593, Definition, text): the **subbase**
`sBase(V) = {x ∈ V₊ | τ x ≤ 1}`, with weight `τ`. -/
abbrev SubB (V : OVSt) : Type := {x : V.carrier // 0 ≤ x ∧ V.tr x ≤ 1}

namespace SubB

variable {V : OVSt}

theorem ext {a b : SubB V} (h : a.1 = b.1) : a = b := Subtype.ext h

theorem tr_nonneg (a : SubB V) : 0 ≤ V.tr a.1 := V.tr_nonneg a.2.1

/-- The partial sum of the subbase: `x ⊥ y` iff `τ x + τ y ≤ 1`, and then
`x ⊕ y = x + y`. -/
instance pcm : PCM (SubB V) where
  zero := ⟨0, le_rfl, by rw [map_zero]; exact zero_le_one⟩
  Perp a b := V.tr a.1 + V.tr b.1 ≤ 1
  ovee a b h := ⟨a.1 + b.1, add_nonneg a.2.1 b.2.1, by rw [map_add]; exact h⟩
  perp_comm h := by rw [add_comm]; exact h
  ovee_comm h := ext (add_comm _ _)
  perp_of_ovee_perp {a b c} _ h := by
    have h' : V.tr (a.1 + b.1) + V.tr c.1 ≤ 1 := h
    rw [map_add] at h'; linarith [tr_nonneg a]
  perp_ovee_of_ovee_perp {a b c} _ h := by
    have h' : V.tr (a.1 + b.1) + V.tr c.1 ≤ 1 := h
    show V.tr a.1 + V.tr (b.1 + c.1) ≤ 1
    rw [map_add] at h' ⊢; linarith
  ovee_assoc _ _ := ext (add_assoc _ _ _)
  zero_perp a := by show V.tr 0 + V.tr a.1 ≤ 1; rw [map_zero, zero_add]; exact a.2.2
  zero_ovee a := ext (zero_add _)

@[simp] theorem zero_val : ((0 : SubB V)).1 = 0 := rfl
theorem perp_iff {a b : SubB V} : Perp a b ↔ V.tr a.1 + V.tr b.1 ≤ 1 := Iff.rfl
@[simp] theorem ovee_val {a b : SubB V} (h : Perp a b) : (ovee a b h).1 = a.1 + b.1 := rfl

/-- The weight module structure of the subbase: `r · x = r x`, `|x| = τ x`. -/
noncomputable instance wmod : WeightMod (SubB V) where
  smul r x := ⟨(r : ℝ) • x.1, smul_nonneg r.2.1 x.2.1, by
    rw [map_smul, smul_eq_mul]
    exact le_trans (mul_le_of_le_one_left (tr_nonneg x) r.2.2) x.2.2⟩
  wt x := ⟨V.tr x.1, tr_nonneg x, x.2.2⟩
  mul_smul l m a := ext (mul_smul (l : ℝ) (m : ℝ) a.1)
  one_smul a := ext (one_smul ℝ a.1)
  smul_perp l a b h := ⟨by
      show V.tr ((l : ℝ) • a.1) + V.tr ((l : ℝ) • b.1) ≤ 1
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add]
      exact le_trans (mul_le_of_le_one_left (add_nonneg (tr_nonneg a) (tr_nonneg b)) l.2.2) h,
    ext (smul_add (l : ℝ) a.1 b.1).symm⟩
  perp_smul {l m} h a := ⟨by
      have h' : (l : ℝ) + m ≤ 1 := h
      show V.tr ((l : ℝ) • a.1) + V.tr ((m : ℝ) • a.1) ≤ 1
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← add_mul]
      exact le_trans (mul_le_of_le_one_left (tr_nonneg a) h') a.2.2,
    ext (add_smul (l : ℝ) (m : ℝ) a.1).symm⟩
  smul_zero l := ext (smul_zero (l : ℝ))
  zero_smul a := ext (zero_smul ℝ a.1)
  wt_zero := Subtype.ext (show V.tr 0 = 0 from map_zero _)
  wt_ovee h := show V.tr (_ + _) = _ from map_add _ _ _
  wt_smul l a := Subtype.ext (show V.tr ((l : ℝ) • a.1) = (l : ℝ) * V.tr a.1 by
    rw [map_smul, smul_eq_mul])
  eq_zero_of_wt a h := by
    have h' : V.tr a.1 = 0 := congrArg Subtype.val h
    refine ext ?_
    rcases a.2.1.lt_or_eq with hlt | heq
    · exact absurd h' (V.tr_pos _ hlt).ne'
    · exact heq.symm
  perp_of_wt h := h

@[simp] theorem smul_val (r : I) (a : SubB V) : (r • a).1 = (r : ℝ) • a.1 := rfl
@[simp] theorem wt_val (a : SubB V) : ((wt a : I) : ℝ) = V.tr a.1 := rfl

/-- **SIG 57** (main.tex:1596, Definition, text): the subbase is cancellative. -/
theorem cancellative : WeightMod.Cancellative (SubB V) := by
  intro x y z hy hz h
  exact ext (add_left_cancel (congrArg Subtype.val h : x.1 + y.1 = x.1 + z.1))

end SubB

/-- **SIG 57** (main.tex:1598, Definition, text): the category `CWMod[[0,1]]`
of cancellative weight `[0,1]`-modules (a full subcategory of `WMod[[0,1]]`). -/
structure CWMod : Type 1 where
  carrier : Type
  [pcm : PCM carrier]
  [wm : WeightMod carrier]
  cancel : WeightMod.Cancellative carrier

attribute [instance] CWMod.pcm CWMod.wm

namespace CWMod

/-- **SIG 57** (SIG 30 at `M = [0,1]`): a morphism of `WMod[[0,1]]`: an
additive, action-preserving, weight-decreasing map. -/
@[ext]
structure Hom (X Y : CWMod) where
  toFun : X.carrier → Y.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : I) (x : X.carrier), toFun (r • x) = r • toFun x
  wt_le : ∀ x, ((wt (toFun x) : I) : ℝ) ≤ wt x

instance : Category CWMod where
  Hom := Hom
  id X := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ => le_rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun r a => by simp [f.map_smul, g.map_smul],
    fun x => (g.wt_le _).trans (f.wt_le x)⟩

@[simp] theorem id_toFun (X : CWMod) : (𝟙 X : Hom X X).toFun = id := rfl
@[simp] theorem comp_toFun {X Y Z : CWMod} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {X Y : CWMod} {f g : X ⟶ Y} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_ovee {X Y : CWMod} (f : X ⟶ Y) {a b : X.carrier} (h : Perp a b) :
    ∃ h' : Perp (f.toFun a) (f.toFun b), ovee _ _ h' = f.toFun (ovee a b h) :=
  f.additive.2 h

end CWMod

/-- **SIG 57** (main.tex:1600, Definition, text): the functor
`sBase : OVSt → CWMod[[0,1]]`. -/
noncomputable abbrev sBase : OVSt ⥤ CWMod where
  obj V := ⟨SubB V, SubB.cancellative⟩
  map {V W} f :=
    { toFun := fun x => ⟨f.toLin x.1, f.pos _ x.2.1, (f.tr_le _ x.2.1).trans x.2.2⟩
      additive := ⟨SubB.ext (map_zero f.toLin), fun {a b} h =>
        ⟨show W.tr (f.toLin a.1) + W.tr (f.toLin b.1) ≤ 1 by
          have h' : V.tr a.1 + V.tr b.1 ≤ 1 := h
          linarith [f.tr_le _ a.2.1, f.tr_le _ b.2.1],
         SubB.ext (map_add f.toLin a.1 b.1).symm⟩⟩
      map_smul := fun r x => SubB.ext (map_smul f.toLin (r : ℝ) x.1)
      wt_le := fun x => f.tr_le _ x.2.1 }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem sBase_map_val {V W : OVSt} (f : V ⟶ W) (x : SubB V) :
    ((sBase.map f).toFun x).1 = f.toLin x.1 := rfl


/-! ## SIG 58: `OVSt ≃ CWMod[[0,1]]` -/

namespace CW

/-- A map on the positive cone of a positively generated ordered vector space
that is additive and `ℝ≥0`-homogeneous extends to a linear map. -/
theorem exists_linear_of_cone {V W : Type*} [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [AddCommGroup W] [Module ℝ W]
    (gen : ∀ x : V, ∃ a b : V, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b) (g : V → W)
    (hadd : ∀ a b : V, 0 ≤ a → 0 ≤ b → g (a + b) = g a + g b)
    (hsmul : ∀ (c : ℝ) (a : V), 0 ≤ c → 0 ≤ a → g (c • a) = c • g a) :
    ∃ F : V →ₗ[ℝ] W, ∀ a, 0 ≤ a → F a = g a := by
  choose pa pb hpa hpb hx using gen
  have wd : ∀ a b a' b' : V, 0 ≤ a → 0 ≤ b → 0 ≤ a' → 0 ≤ b' → a - b = a' - b' →
      g a - g b = g a' - g b' := by
    intro a b a' b' ha hb ha' hb' h
    have e : a + b' = a' + b := by
      rw [← sub_eq_sub_iff_add_eq_add]; exact h
    have := congrArg g e
    rw [hadd _ _ ha hb', hadd _ _ ha' hb] at this
    rw [sub_eq_sub_iff_add_eq_add]; exact this
  have g0 : g 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at this
    exact left_eq_add.mp this
  have key : ∀ x a b : V, 0 ≤ a → 0 ≤ b → x = a - b → g (pa x) - g (pb x) = g a - g b :=
    fun x a b ha hb h => wd _ _ _ _ (hpa x) (hpb x) ha hb ((hx x).symm.trans h)
  refine ⟨{ toFun := fun x => g (pa x) - g (pb x), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    rw [key (x + y) (pa x + pa y) (pb x + pb y) (add_nonneg (hpa x) (hpa y))
      (add_nonneg (hpb x) (hpb y)) (by
        conv_lhs => rw [hx x, hx y]
        abel),
      hadd _ _ (hpa x) (hpa y), hadd _ _ (hpb x) (hpb y)]
    abel
  · intro c x
    simp only [RingHom.id_apply]
    rcases le_total 0 c with hc | hc
    · rw [key (c • x) (c • pa x) (c • pb x) (smul_nonneg hc (hpa x)) (smul_nonneg hc (hpb x))
        (by rw [← smul_sub, ← hx x]), hsmul c _ hc (hpa x), hsmul c _ hc (hpb x), smul_sub]
    · have hc' : 0 ≤ -c := by linarith
      rw [key (c • x) ((-c) • pb x) ((-c) • pa x) (smul_nonneg hc' (hpb x))
        (smul_nonneg hc' (hpa x)) (by rw [← smul_sub, neg_smul, ← smul_neg, neg_sub, ← hx x]),
        hsmul _ _ hc' (hpb x), hsmul _ _ hc' (hpa x), smul_sub, neg_smul, neg_smul]
      abel
  · intro a ha
    show g (pa a) - g (pb a) = g a
    rw [key a a 0 ha le_rfl (sub_zero a).symm, g0, sub_zero]

end CW

namespace OVSt

variable {V : OVSt}

theorem tr_div_le {x : V.carrier} (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) (hle : V.tr x ≤ t) :
    V.tr (t⁻¹ • x) ≤ 1 := by
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]; exact hle

/-- `t⁻¹ x ∈ sBase V` for `x ≥ 0` and `τ x ≤ t`. -/
noncomputable def sc (x : V.carrier) (hx : 0 ≤ x) (t : ℝ) (ht : 0 < t) (hle : V.tr x ≤ t) :
    SubB V :=
  ⟨t⁻¹ • x, smul_nonneg (inv_nonneg.2 ht.le) hx, tr_div_le hx ht hle⟩

theorem smul_sc (x : V.carrier) (hx : 0 ≤ x) (t : ℝ) (ht : 0 < t) (hle : V.tr x ≤ t) :
    t • (sc x hx t ht hle).1 = x := by
  show t • t⁻¹ • x = x
  rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

theorem tr_le_succ {x : V.carrier} : V.tr x ≤ |V.tr x| + 1 := by
  linarith [le_abs_self (V.tr x)]

theorem succ_pos (x : V.carrier) : 0 < |V.tr x| + 1 := by positivity

/-- Linear maps out of `V` agree once they agree on the subbase. -/
theorem linear_ext_subB {W : Type*} [AddCommGroup W] [Module ℝ W]
    {F G : V.carrier →ₗ[ℝ] W} (h : ∀ a : SubB V, F a.1 = G a.1) : F = G := by
  have hpos : ∀ a : V.carrier, 0 ≤ a → F a = G a := by
    intro a ha
    rw [← smul_sc a ha _ (succ_pos a) tr_le_succ, map_smul, map_smul, h]
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, b, ha, hb, rfl⟩ := V.gen x
  rw [map_sub, map_sub, hpos a ha, hpos b hb]

end OVSt

section Full

variable {V W : OVSt} (f : sBase.obj V ⟶ sBase.obj W)

theorem cw_sc_eq_smul (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (hle : V.tr x ≤ t) :
    OVSt.sc x hx t' (ht.trans_le htt) (hle.trans htt)
      = (⟨t / t', ⟨div_nonneg ht.le (ht.le.trans htt), (div_le_one (ht.trans_le htt)).2 htt⟩⟩ : I)
        • OVSt.sc x hx t ht hle := by
  refine SubB.ext ?_
  show t'⁻¹ • x = (t / t') • t⁻¹ • x
  rw [smul_smul]
  congr 1
  have : t' ≠ 0 := (ht.trans_le htt).ne'
  field_simp

theorem cw_scale_mono (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (hle : V.tr x ≤ t) :
    t' • (f.toFun (OVSt.sc x hx t' (ht.trans_le htt) (hle.trans htt))).1
      = t • (f.toFun (OVSt.sc x hx t ht hle)).1 := by
  rw [cw_sc_eq_smul x hx ht htt hle, f.map_smul, SubB.smul_val, smul_smul]
  congr 1
  show t' * (t / t') = t
  have : t' ≠ 0 := (ht.trans_le htt).ne'
  field_simp

theorem cw_scale_indep (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (hle : V.tr x ≤ t) (hle' : V.tr x ≤ t') :
    t • (f.toFun (OVSt.sc x hx t ht hle)).1 = t' • (f.toFun (OVSt.sc x hx t' ht' hle')).1 := by
  rw [← cw_scale_mono f x hx ht (le_max_left t t') hle,
    ← cw_scale_mono f x hx ht' (le_max_right t t') hle']

open Classical in
/-- The extension of `f` to the positive cone. -/
noncomputable def cwExtG (x : V.carrier) : W.carrier :=
  if hx : 0 ≤ x then (|V.tr x| + 1) • (f.toFun (OVSt.sc x hx _ (OVSt.succ_pos x) OVSt.tr_le_succ)).1
  else 0

theorem cwExtG_eq (x : V.carrier) (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) (hle : V.tr x ≤ t) :
    cwExtG f x = t • (f.toFun (OVSt.sc x hx t ht hle)).1 := by
  rw [cwExtG, dite_cond_eq_true (eq_true hx)]; exact cw_scale_indep f x hx _ ht _ hle

theorem cwExtG_nonneg (x : V.carrier) : 0 ≤ cwExtG f x := by
  unfold cwExtG; split_ifs with hx
  · exact smul_nonneg (OVSt.succ_pos x).le (f.toFun _).2.1
  · exact le_rfl

theorem cwExtG_add (a b : V.carrier) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cwExtG f (a + b) = cwExtG f a + cwExtG f b := by
  have hta := V.tr_nonneg ha; have htb := V.tr_nonneg hb
  set T := V.tr a + V.tr b + 1 with hT
  have hT0 : 0 < T := by positivity
  have hp : Perp (OVSt.sc a ha T hT0 (by linarith)) (OVSt.sc b hb T hT0 (by linarith)) := by
    show V.tr (T⁻¹ • a) + V.tr (T⁻¹ • b) ≤ 1
    rw [← map_add, ← smul_add]
    exact OVSt.tr_div_le (add_nonneg ha hb) hT0 (by rw [map_add]; linarith)
  have e : OVSt.sc (a + b) (add_nonneg ha hb) T hT0 (by rw [map_add]; linarith)
      = ovee _ _ hp := SubB.ext (smul_add _ _ _)
  rw [cwExtG_eq f _ (add_nonneg ha hb) hT0 (by rw [map_add]; linarith), e,
    cwExtG_eq f a ha hT0 (by linarith), cwExtG_eq f b hb hT0 (by linarith), ← smul_add]
  obtain ⟨_, e'⟩ := f.map_ovee hp
  rw [← e']; rfl

theorem cwExtG_zero : cwExtG f (0 : V.carrier) = 0 := by
  have := cwExtG_add f 0 0 le_rfl le_rfl
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem cwExtG_smul (c : ℝ) (a : V.carrier) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    cwExtG f (c • a) = c • cwExtG f a := by
  rcases hc.lt_or_eq with hc | hc
  · have hta := V.tr_nonneg ha
    have hT : 0 < V.tr a + 1 := by positivity
    have h1 : 0 < c * (V.tr a + 1) := by positivity
    have hle : V.tr (c • a) ≤ c * (V.tr a + 1) := by rw [map_smul, smul_eq_mul]; nlinarith
    have e : OVSt.sc (c • a) (smul_nonneg hc.le ha) _ h1 hle
        = OVSt.sc a ha _ hT (by linarith) := by
      refine SubB.ext ?_
      show (c * (V.tr a + 1))⁻¹ • c • a = (V.tr a + 1)⁻¹ • a
      rw [smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
    rw [cwExtG_eq f a ha hT (by linarith), cwExtG_eq f (c • a) (smul_nonneg hc.le ha) h1 hle, e,
      smul_smul]
  · rw [← hc, zero_smul, zero_smul, cwExtG_zero]

theorem cwExtG_subB (y : SubB V) : cwExtG f y.1 = (f.toFun y).1 := by
  rw [cwExtG_eq f y.1 y.2.1 one_pos y.2.2, one_smul]
  congr 2
  exact SubB.ext (by show (1 : ℝ)⁻¹ • y.1 = y.1; rw [inv_one, one_smul])

theorem cwExtG_tr_le (x : V.carrier) (hx : 0 ≤ x) : W.tr (cwExtG f x) ≤ V.tr x := by
  rw [cwExtG_eq f x hx (OVSt.succ_pos x) OVSt.tr_le_succ, map_smul, smul_eq_mul]
  have := f.wt_le (OVSt.sc x hx _ (OVSt.succ_pos x) OVSt.tr_le_succ)
  rw [SubB.wt_val, SubB.wt_val] at this
  calc (|V.tr x| + 1) * W.tr (f.toFun _).1 ≤ (|V.tr x| + 1) * V.tr ((|V.tr x| + 1)⁻¹ • x) :=
        mul_le_mul_of_nonneg_left this (OVSt.succ_pos x).le
    _ = V.tr x := by
        rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (OVSt.succ_pos x).ne', one_mul]

/-- The extension of a `CWMod`-morphism `sBase V → sBase W` to `V → W`. -/
noncomputable def cwExtHom : V ⟶ W :=
  let hF := CW.exists_linear_of_cone V.gen (cwExtG f) (cwExtG_add f) (cwExtG_smul f)
  { toLin := hF.choose
    pos := fun x hx => by rw [hF.choose_spec x hx]; exact cwExtG_nonneg f x
    tr_le := fun x hx => by rw [hF.choose_spec x hx]; exact cwExtG_tr_le f x hx }

theorem cwExtHom_apply (x : V.carrier) (hx : 0 ≤ x) : (cwExtHom f).toLin x = cwExtG f x :=
  (CW.exists_linear_of_cone V.gen (cwExtG f) (cwExtG_add f) (cwExtG_smul f)).choose_spec x hx

theorem sBase_map_extHom : sBase.map (cwExtHom f) = f := by
  refine CWMod.hom_ext fun y => SubB.ext ?_
  rw [sBase_map_val, cwExtHom_apply f y.1 y.2.1, cwExtG_subB]

end Full

instance sBase_faithful : sBase.Faithful where
  map_injective {V W} f g h := by
    refine OVSt.hom_ext fun x => ?_
    have := OVSt.linear_ext_subB (F := f.toLin) (G := g.toLin) fun a => by
      have := congrArg (fun φ : sBase.obj V ⟶ sBase.obj W => (φ.toFun a).1) h
      simpa using this
    rw [this]

instance sBase_full : sBase.Full where
  map_surjective f := ⟨cwExtHom f, sBase_map_extHom f⟩

/-- The ordered vector space with trace `V(X)` of a cancellative weight
`[0,1]`-module (the construction of the print's proof of SIG 58, by formal
multiples and differences). -/
noncomputable def vOf (X : CWMod) : OVSt :=
  haveI : Fact (WeightMod.Cancellative X.carrier) := ⟨X.cancel⟩
  { carrier := CW.Vec X.carrier
    gen := CW.Vec.gen
    tr := CW.Vec.tr
    tr_pos := fun _ h => CW.Vec.tr_pos h }

section Ess

variable (X : CWMod)

instance : Fact (WeightMod.Cancellative X.carrier) := ⟨X.cancel⟩

/-- `a ↦ 1 · a`, as a morphism `X → sBase V(X)`. -/
noncomputable def toVOf : X ⟶ sBase.obj (vOf X) where
  toFun a := ⟨CW.gmap a, CW.gmap_nonneg a, by
    show CW.Vec.tr (CW.gmap a) ≤ 1
    rw [CW.tr_gmap]; exact (wt a).2.2⟩
  additive := ⟨SubB.ext CW.gmap_zero, fun {a b} h =>
    ⟨show CW.Vec.tr (CW.gmap a) + CW.Vec.tr (CW.gmap b) ≤ 1 from CW.gmap_perp_iff.1 h,
      SubB.ext (CW.gmap_ovee h).symm⟩⟩
  map_smul r a := SubB.ext (CW.gmap_smul r a)
  wt_le a := by
    show CW.Vec.tr (CW.gmap a) ≤ _
    rw [CW.tr_gmap]

theorem cw_exists_gmap (x : SubB (vOf X)) : ∃ a : X.carrier, CW.gmap a = x.1 :=
  CW.gmap_surjective (X := X.carrier) x.2.1 x.2.2

/-- The inverse of `toVOf`. -/
noncomputable def fromVOf : sBase.obj (vOf X) ⟶ X where
  toFun x := (cw_exists_gmap X x).choose
  additive := by
    have hs := fun x => (cw_exists_gmap X x).choose_spec
    refine ⟨CW.gmap_injective (by rw [hs 0, CW.gmap_zero]; rfl), fun {x y} h => ?_⟩
    have hp : Perp (cw_exists_gmap X x).choose (cw_exists_gmap X y).choose := by
      rw [CW.gmap_perp_iff, hs x, hs y]; exact h
    refine ⟨hp, CW.gmap_injective ?_⟩
    rw [CW.gmap_ovee, hs x, hs y, hs]; rfl
  map_smul r x := by
    have hs := fun x => (cw_exists_gmap X x).choose_spec
    refine CW.gmap_injective ?_
    rw [CW.gmap_smul, hs, hs]; rfl
  wt_le x := by
    have := CW.tr_gmap (X := X.carrier) (cw_exists_gmap X x).choose
    rw [(cw_exists_gmap X x).choose_spec] at this
    rw [← this]; exact le_rfl

/-- `sBase V(X) ≅ X`. -/
noncomputable def vOfIso : sBase.obj (vOf X) ≅ X where
  hom := fromVOf X
  inv := toVOf X
  hom_inv_id := CWMod.hom_ext fun x => SubB.ext (cw_exists_gmap X x).choose_spec
  inv_hom_id := CWMod.hom_ext fun a => CW.gmap_injective (X := X.carrier)
    (cw_exists_gmap X ((toVOf X).toFun a)).choose_spec

end Ess

instance sBase_essSurj : sBase.EssSurj := ⟨fun X => ⟨vOf X, ⟨vOfIso X⟩⟩⟩

/-- **SIG 58** (`prop:OVSt-equiv-CWMod`, main.tex:1605, Proposition): the
functor `sBase : OVSt → CWMod[[0,1]]` is an equivalence of categories.  The
print sketches the inverse (totalization of `X`, then formal differences) and
refers to Cho's thesis §7.2.1; ours builds `V(X)` as formal multiples `r · a`
modulo rescaling, then formal differences (the tree's Gudder–Pulmannová route,
179III.2, with sums made total by the weight), and proves fullness by
extending a morphism from the subbase to the positive cone and then linearly. -/
instance sBase_isEquivalence : sBase.IsEquivalence where


/-! ## Canonical sums in `[0,1]` are real sums -/

namespace CW

theorem isSumOf_I_iff (l : List I) (s : I) :
    PCM.IsSumOf l s ↔ (s : ℝ) = (l.map (fun a : I => (a : ℝ))).sum := by
  induction l generalizing s with
  | nil =>
    rw [PCM.isSumOf_nil_iff, List.map_nil, List.sum_nil]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | cons a l ih =>
    rw [PCM.isSumOf_cons_iff, List.map_cons, List.sum_cons]
    constructor
    · rintro ⟨t, ht, h, rfl⟩
      rw [GP.I_coe_ovee, (ih t).1 ht]
    · intro hs
      have h0 : 0 ≤ (l.map (fun a : I => (a : ℝ))).sum :=
        List.sum_nonneg (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact b.2.1)
      have h1 : (l.map (fun a : I => (a : ℝ))).sum ≤ 1 := by linarith [a.2.1, s.2.2]
      refine ⟨⟨_, h0, h1⟩, (ih _).2 rfl, ?_, Subtype.ext ?_⟩
      · show (a : ℝ) + _ ≤ 1; linarith [s.2.2]
      · rw [GP.I_coe_ovee]; exact hs.symm

theorem finSum_I_iff {J : Type} (x : J → I) (F : Finset J) (s : I) :
    FinSum x F s ↔ (s : ℝ) = ∑ j ∈ F, (x j : ℝ) := by
  unfold FinSum
  rw [isSumOf_I_iff, List.map_map]
  exact Iff.of_eq (congrArg (fun r => (s : ℝ) = r) (Finset.sum_map_toList F (fun j => (x j : ℝ))))

theorem csummable_I_iff {J : Type} (x : J → I) :
    CSummable x ↔ ∀ F : Finset J, ∑ j ∈ F, (x j : ℝ) ≤ 1 := by
  constructor
  · intro h F
    obtain ⟨s, hs⟩ := h F
    rw [← (finSum_I_iff x F s).1 hs]; exact s.2.2
  · intro h F
    exact ⟨⟨_, Finset.sum_nonneg fun j _ => (x j).2.1, h F⟩, (finSum_I_iff _ _ _).2 rfl⟩

theorem isCSum_I_iff {J : Type} (x : J → I) (s : I) :
    IsCSum x s ↔ CSummable x ∧ HasSum (fun j => (x j : ℝ)) s := by
  have h0 : ∀ j, 0 ≤ (x j : ℝ) := fun j => (x j).2.1
  have key : CSummable x → (IsSupOf {t | ∃ F, FinSum x F t} s ↔
      IsLUB (Set.range fun F : Finset J => ∑ j ∈ F, (x j : ℝ)) s) := by
    intro hc
    have hc' := (csummable_I_iff x).1 hc
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by
        rintro _ ⟨F, rfl⟩
        exact unitInterval_le_iff.1 (h1 ⟨_, Finset.sum_nonneg fun j _ => h0 j, hc' F⟩
          ⟨F, (finSum_I_iff _ _ _).2 rfl⟩), fun c hc => ?_⟩
      by_cases hc1 : c ≤ 1
      · have hc0 : 0 ≤ c := le_trans (by simp) (hc ⟨∅, rfl⟩)
        refine unitInterval_le_iff.1 (h2 ⟨c, hc0, hc1⟩ ?_)
        rintro t ⟨F, hF⟩
        rw [unitInterval_le_iff, (finSum_I_iff _ _ _).1 hF]
        exact hc ⟨F, rfl⟩
      · exact le_trans s.2.2 (le_of_lt (not_le.1 hc1))
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ⟨F, hF⟩ => ?_, fun c hc => ?_⟩
      · rw [unitInterval_le_iff, (finSum_I_iff _ _ _).1 hF]; exact h1 ⟨F, rfl⟩
      · rw [unitInterval_le_iff]
        refine h2 ?_
        rintro _ ⟨F, rfl⟩
        exact unitInterval_le_iff.1 (hc _ ⟨F, (finSum_I_iff (s := ⟨_, Finset.sum_nonneg
          fun j _ => h0 j, hc' F⟩) _ _).2 rfl⟩)
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨hc, hasSum_of_isLUB_of_nonneg _ h0 ((key hc).1 hs)⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hc, (key hc).2 (isLUB_hasSum h0 hs)⟩

theorem hasSum_of_isCSum {J : Type} {x : J → I} {s : I} (h : IsCSum x s) :
    HasSum (fun j => (x j : ℝ)) s := ((isCSum_I_iff x s).1 h).2

theorem isCSum_of_hasSum {J : Type} {x : J → I} {s : I} (h : HasSum (fun j => (x j : ℝ)) s) :
    IsCSum x s := by
  refine (isCSum_I_iff x s).2 ⟨(csummable_I_iff x).2 fun F => ?_, h⟩
  exact le_trans (sum_le_hasSum F (fun j _ => (x j).2.1) h) s.2.2

end CW

/-! ## SIG 57: the base norm; pre-base-norm, Banach, σ-closed subbase -/

namespace OVSt

variable (V : OVSt)

/-- The values `τ x₁ + τ x₂` over decompositions `x = x₁ - x₂`, `xᵢ ≥ 0`. -/
def normSet (x : V.carrier) : Set ℝ :=
  {r | ∃ a b : V.carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b ∧ r = V.tr a + V.tr b}

/-- **SIG 57** (main.tex:1612, Definition, text): the intrinsic seminorm (base norm)
`‖x‖ = inf {τ x₁ + τ x₂ | x = x₁ - x₂, x₁, x₂ ∈ V₊}`. -/
noncomputable def bnorm (x : V.carrier) : ℝ := sInf (V.normSet x)

/-- **SIG 57** (main.tex:1622, Definition, text): `V` is a **pre-base-norm space** if the
seminorm is a norm. -/
def IsPreBaseNorm : Prop := ∀ x : V.carrier, V.bnorm x = 0 → x = 0

/-- Completeness for the base (semi)norm: Cauchy sequences converge. -/
def BNComplete : Prop :=
  ∀ s : ℕ → V.carrier, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, V.bnorm (s m - s n) < ε) →
    ∃ v : V.carrier, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, V.bnorm (s n - v) < ε

/-- **SIG 57** (main.tex:1625, Definition, text): a **Banach pre-base-norm space**: a
pre-base-norm space complete in the base norm. -/
def IsBanachPBN : Prop := V.IsPreBaseNorm ∧ V.BNComplete

/-- The series `∑ₙ xₙ` converges to `v` in the base norm. -/
def SeriesTo (x : ℕ → V.carrier) (v : V.carrier) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, V.bnorm ((∑ i ∈ Finset.range n, x i) - v) < ε

/-- **SIG 57** (main.tex:1630, Definition, text): a **σ-closed subbase**: for every sequence
`(xₙ)` in `sBase(V)` with `∑ τ(xₙ) ≤ 1` the series `∑ xₙ` converges to an
element of `sBase(V)`. -/
def SigmaClosedSubbase : Prop :=
  ∀ x : ℕ → V.carrier, (∀ n, 0 ≤ x n) → (∀ N, ∑ i ∈ Finset.range N, V.tr (x i) ≤ 1) →
    ∃ v : V.carrier, 0 ≤ v ∧ V.tr v ≤ 1 ∧ V.SeriesTo x v

variable {V}

theorem normSet_nonempty (x : V.carrier) : (V.normSet x).Nonempty := by
  obtain ⟨a, b, ha, hb, h⟩ := V.gen x
  exact ⟨_, a, b, ha, hb, h, rfl⟩

theorem normSet_bdd (x : V.carrier) : BddBelow (V.normSet x) :=
  ⟨0, by rintro _ ⟨a, b, ha, hb, -, rfl⟩; exact add_nonneg (V.tr_nonneg ha) (V.tr_nonneg hb)⟩

theorem bnorm_nonneg (x : V.carrier) : 0 ≤ V.bnorm x :=
  le_csInf (normSet_nonempty x) (by
    rintro _ ⟨a, b, ha, hb, -, rfl⟩; exact add_nonneg (V.tr_nonneg ha) (V.tr_nonneg hb))

theorem bnorm_le {x a b : V.carrier} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x = a - b) :
    V.bnorm x ≤ V.tr a + V.tr b :=
  csInf_le (normSet_bdd x) ⟨a, b, ha, hb, h, rfl⟩

theorem exists_lt_of_bnorm_lt {x : V.carrier} {ε : ℝ} (hε : V.bnorm x < ε) :
    ∃ a b : V.carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b ∧ V.tr a + V.tr b < ε := by
  obtain ⟨r, ⟨a, b, ha, hb, h, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (normSet_nonempty x) hε
  exact ⟨a, b, ha, hb, h, hr⟩

theorem le_bnorm {x : V.carrier} {c : ℝ}
    (h : ∀ a b : V.carrier, 0 ≤ a → 0 ≤ b → x = a - b → c ≤ V.tr a + V.tr b) :
    c ≤ V.bnorm x :=
  le_csInf (normSet_nonempty x) (by rintro _ ⟨a, b, ha, hb, hx, rfl⟩; exact h a b ha hb hx)

/-- **SIG 73** (proof, main.tex:3386, citing Furber Cor. 2.2.5): on the
positive cone the base norm is the trace. -/
theorem bnorm_of_nonneg {x : V.carrier} (hx : 0 ≤ x) : V.bnorm x = V.tr x := by
  refine le_antisymm ?_ (le_bnorm fun a b ha hb h => ?_)
  · have := bnorm_le hx le_rfl (sub_zero x).symm
    rwa [map_zero, add_zero] at this
  · rw [h, map_sub]; linarith [V.tr_nonneg hb]

theorem bnorm_zero : V.bnorm 0 = 0 := by rw [bnorm_of_nonneg le_rfl, map_zero]

theorem abs_tr_le (x : V.carrier) : |V.tr x| ≤ V.bnorm x :=
  le_bnorm fun a b ha hb h => by
    rw [h, map_sub, abs_le]
    constructor <;> linarith [V.tr_nonneg ha, V.tr_nonneg hb]

theorem bnorm_add_le (x y : V.carrier) : V.bnorm (x + y) ≤ V.bnorm x + V.bnorm y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, b, ha, hb, hx, h1⟩ := exists_lt_of_bnorm_lt
    (lt_add_of_pos_right (V.bnorm x) (half_pos hε))
  obtain ⟨c, d, hc, hd, hy, h2⟩ := exists_lt_of_bnorm_lt
    (lt_add_of_pos_right (V.bnorm y) (half_pos hε))
  calc V.bnorm (x + y) ≤ V.tr (a + c) + V.tr (b + d) :=
        bnorm_le (add_nonneg ha hc) (add_nonneg hb hd) (by rw [hx, hy]; abel)
    _ < V.bnorm x + V.bnorm y + ε := by rw [map_add, map_add]; linarith

theorem bnorm_neg (x : V.carrier) : V.bnorm (-x) = V.bnorm x := by
  have : ∀ y : V.carrier, V.bnorm (-y) ≤ V.bnorm y := fun y =>
    le_bnorm fun a b ha hb h => by
      have := bnorm_le (x := -y) hb ha (by rw [h]; abel)
      linarith
  exact le_antisymm (this x) (by simpa using this (-x))

theorem bnorm_sub_comm (x y : V.carrier) : V.bnorm (x - y) = V.bnorm (y - x) := by
  rw [← bnorm_neg, neg_sub]

theorem bnorm_smul_le {c : ℝ} (hc : 0 ≤ c) (x : V.carrier) : V.bnorm (c • x) ≤ c * V.bnorm x := by
  rcases hc.lt_or_eq with hc | hc
  · have : c⁻¹ * V.bnorm (c • x) ≤ V.bnorm x := le_bnorm fun a b ha hb h => by
      have := bnorm_le (x := c • x) (smul_nonneg hc.le ha) (smul_nonneg hc.le hb)
        (by rw [h, smul_sub])
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add] at this
      rw [inv_mul_le_iff₀ hc]; exact this
    rwa [inv_mul_le_iff₀ hc] at this
  · rw [← hc, zero_smul, zero_mul, bnorm_zero]

theorem bnorm_smul (c : ℝ) (x : V.carrier) : V.bnorm (c • x) = |c| * V.bnorm x := by
  have key : ∀ {c : ℝ}, 0 ≤ c → ∀ x : V.carrier, V.bnorm (c • x) = c * V.bnorm x := by
    intro c hc x
    refine le_antisymm (bnorm_smul_le hc x) ?_
    rcases hc.lt_or_eq with hc | hc
    · have := bnorm_smul_le (inv_nonneg.2 hc.le) (c • x)
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      rw [← le_div_iff₀' hc, div_eq_inv_mul]; exact this
    · rw [← hc, zero_mul]; exact bnorm_nonneg _
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, key hc]
  · rw [abs_of_nonpos hc, show c • x = (-c) • (-x) by rw [smul_neg, neg_smul, neg_neg],
      key (neg_nonneg.2 hc), bnorm_neg]

end OVSt


/-! ## SIG 73: a σ-weight module structure on the subbase makes `V` a Banach
pre-base-norm space -/

/-- **SIG 57** (main.tex:1643, Definition, text): a σ-weight module is
**cancellative** if `x ⊕ y = x ⊕ z` implies `y = z`. -/
def SWMod.IsCancellative {M : Type uw} [EffectMonoid M] (X : SWMod M) : Prop :=
  ∀ x y z s : X.carrier, SigmaPAM.SumsTo ![x, y] s → SigmaPAM.SumsTo ![x, z] s → y = z

theorem SubB.val_eq_zero_of_tr {V : OVSt} (a : SubB V) (h : V.tr a.1 = 0) : a.1 = 0 := by
  rcases a.2.1.lt_or_eq with hlt | heq
  · exact absurd h (V.tr_pos _ hlt).ne'
  · exact heq.symm

/-- The σ-weight `[0,1]`-module `X` is a structure on `sBase(V)` **extending**
its weight-module structure (SIG 73's hypothesis), presented by a bijection
`e : X ≃ sBase(V)` preserving the action, the weight, and binary sums. -/
structure SigmaExtension (V : OVSt) (X : SWMod I) where
  e : X.carrier ≃ SubB V
  map_smul : ∀ (r : I) (x : X.carrier), e (r • x) = r • e x
  wt_eq : ∀ x : X.carrier, ((X.weight x : I) : ℝ) = V.tr (e x).1
  pair : ∀ x y s : X.carrier, SigmaPAM.SumsTo ![x, y] s ↔
    V.tr (e x).1 + V.tr (e y).1 ≤ 1 ∧ (e s).1 = (e x).1 + (e y).1

namespace CW

/-- A family over `ℕ ⊕ ℕ` sums to `U` iff the family of its pair-sums does. -/
def fibEquiv (n : ℕ) : Fin 2 ≃ {j : ℕ ⊕ ℕ // Sum.elim id id j = n} where
  toFun i := if i = 0 then ⟨Sum.inl n, rfl⟩ else ⟨Sum.inr n, rfl⟩
  invFun j := match j with
    | ⟨Sum.inl _, _⟩ => 0
    | ⟨Sum.inr _, _⟩ => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro ⟨(k | k), hk⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, id] at hk <;> subst hk <;> rfl

theorem sumsTo_pairs {M : Type} [SigmaPAM M] (f g P : ℕ → M)
    (hP : ∀ n, SigmaPAM.SumsTo ![f n, g n] (P n)) (U : M) :
    SigmaPAM.SumsTo (Sum.elim f g) U ↔ SigmaPAM.SumsTo P U := by
  have hfib : ∀ n, SigmaPAM.SumsTo
      (fun j : {j : ℕ ⊕ ℕ // Sum.elim id id j = n} => Sum.elim f g j.1) (P n) := by
    intro n
    refine (SigmaPAM.sumsTo_comp_equiv' (fibEquiv n) _ ![f n, g n] ?_ (P n)).1 (hP n)
    intro i; fin_cases i <;> rfl
  rw [SigmaPAM.sumsTo_partition_iff (Sum.elim f g) (Sum.elim id id)]
  constructor
  · rintro ⟨t, ht, htU⟩
    have : t = P := funext fun n => (ht n).unique (hfib n)
    rwa [this] at htU
  · intro h; exact ⟨P, hfib, h⟩

theorem hasSum_geom2 : HasSum (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 2)) (1 / 2) := by
  have h := hasSum_geometric_two.mul_left (1 / 4 : ℝ)
  have e : (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 2)) = fun i => 1 / 4 * ((1 : ℝ) / 2) ^ i := by
    funext n; rw [pow_add]; ring
  have e2 : (1 / 2 : ℝ) = 1 / 4 * 2 := by norm_num
  rw [e]; rw [← e2] at h; exact h

theorem sum_geom_le (g : ℕ → ℝ) (h0 : ∀ n, 0 ≤ g n) (h : ∀ n, g n ≤ (1 / 2) ^ (n + 2))
    (F : Finset ℕ) : ∑ j ∈ F, g j ≤ 1 / 2 := by
  have hs := hasSum_geom2
  calc ∑ j ∈ F, g j ≤ ∑ j ∈ F, ((1 : ℝ) / 2) ^ (j + 2) := Finset.sum_le_sum fun j _ => h j
    _ ≤ 1 / 2 := sum_le_hasSum F (fun _ _ => by positivity) hs

theorem hasSum_geom_le (g : ℕ → ℝ) (h : ∀ n, g n ≤ (1 / 2) ^ (n + 2)) {a : ℝ}
    (ha : HasSum g a) : a ≤ 1 / 2 := by
  have hs := hasSum_geom2
  exact hasSum_le h ha hs

end CW

namespace SigmaExtension

variable {V : OVSt} {X : SWMod I} (E : SigmaExtension V X)

theorem e_zero : (E.e SigmaPAM.zero).1 = 0 :=
  SubB.val_eq_zero_of_tr _ (by rw [← E.wt_eq, X.weight_zero]; rfl)

theorem fin_sum : ∀ (N : ℕ) (f : Fin N → X.carrier) (u : X.carrier), SigmaPAM.SumsTo f u →
    (E.e u).1 = ∑ i, (E.e (f i)).1 := by
  intro N
  induction N with
  | zero =>
    intro f u h
    rw [h.unique (SigmaPAM.sumsTo_of_isEmpty f), E.e_zero, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ N ih =>
    intro f u h
    obtain ⟨u', hu', hp⟩ := (SigmaPAM.sumsTo_fin_last_iff f u).1 h
    rw [((E.pair _ _ _).1 hp).2, ih _ u' hu', Fin.sum_univ_castSucc]

theorem hasSum_tr {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) :
    HasSum (fun n => V.tr (E.e (x n)).1) (V.tr (E.e s).1) := by
  have := CW.hasSum_of_isCSum (X.weight_sumsTo x s h)
  simp only [E.wt_eq] at this
  exact this

theorem sub_nonneg_split {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) (n : ℕ) :
    ∃ v : X.carrier, (E.e s).1 = (∑ i ∈ Finset.range n, (E.e (x i)).1) + (E.e v).1 := by
  obtain ⟨u, v, hu, hv, huv⟩ := (SigmaPAM.sumsTo_split x (· < n) s).1 h
  have hu' : SigmaPAM.SumsTo (fun i : Fin n => x i) u :=
    (SigmaPAM.sumsTo_comp_equiv' Fin.equivSubtype (fun j : {i // i < n} => x j.1)
      (fun i : Fin n => x i) (fun _ => rfl) u).2 hu
  refine ⟨v, ?_⟩
  rw [((E.pair _ _ _).1 huv).2, E.fin_sum n _ u hu', Fin.sum_univ_eq_sum_range
    (fun i => (E.e (x i)).1)]

/-- **SIG 73**, second claim: the series `∑ xₙ` converges to `⋁ xₙ` in the
base norm (proof as printed, with Furber's `‖x‖ = τ x` on `V₊`). -/
theorem seriesTo {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) :
    V.SeriesTo (fun n => (E.e (x n)).1) (E.e s).1 := by
  intro ε hε
  have ht := (E.hasSum_tr h).tendsto_sum_nat
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨v, hv⟩ := E.sub_nonneg_split h n
  have hd := hN n hn
  rw [Real.dist_eq] at hd
  have e1 : (∑ i ∈ Finset.range n, (E.e (x i)).1) - (E.e s).1 = -(E.e v).1 := by
    rw [hv]; abel
  rw [e1, OVSt.bnorm_neg, OVSt.bnorm_of_nonneg (E.e v).2.1]
  have e2 : V.tr (E.e v).1 = V.tr (E.e s).1 - ∑ i ∈ Finset.range n, V.tr (E.e (x i)).1 := by
    rw [hv, map_add, map_sum]; ring
  rw [e2]
  have := abs_sub_comm (∑ i ∈ Finset.range n, V.tr (E.e (x i)).1) (V.tr (E.e s).1)
  exact lt_of_le_of_lt (le_abs_self _) (this ▸ hd)

/-- Elements of `X` from small positive vectors. -/
noncomputable def ofVec (y : V.carrier) (hy : 0 ≤ y) (ht : V.tr y ≤ 1) : X.carrier :=
  E.e.symm (⟨y, hy, ht⟩ : SubB V)

theorem e_ofVec (y : V.carrier) (hy : 0 ≤ y) (ht : V.tr y ≤ 1) :
    (E.e (E.ofVec y hy ht)).1 = y := by
  exact congrArg Subtype.val (E.e.apply_symm_apply _)

/-- A sequence of small positive vectors is summable in `X`. -/
theorem sumsTo_of_small (y : ℕ → V.carrier) (hy : ∀ n, 0 ≤ y n)
    (hs : ∀ n, V.tr (y n) ≤ (1 / 2) ^ (n + 2)) :
    ∃ a : X.carrier, SigmaPAM.SumsTo (fun n => E.ofVec (y n) (hy n)
      ((hs n).trans (by
        have : ((1 : ℝ) / 2) ^ (n + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        exact this))) a ∧ V.tr (E.e a).1 ≤ 1 / 2 := by
  have hsum := X.summable_of_weight (fun n => E.ofVec (y n) (hy n) ((hs n).trans
    (pow_le_one₀ (by norm_num) (by norm_num)))) ((CW.csummable_I_iff _).2 fun F => by
      simp only [E.wt_eq, e_ofVec]
      exact (CW.sum_geom_le _ (fun n => V.tr_nonneg (hy n)) hs F).trans (by norm_num))
  refine ⟨_, SigmaPAM.sumsTo_sum hsum, ?_⟩
  have := E.hasSum_tr (SigmaPAM.sumsTo_sum hsum)
  simp only [e_ofVec] at this
  exact CW.hasSum_geom_le _ hs this

include E in
/-- **SIG 73**, first claim: `V` is a pre-base-norm space (proof as printed;
the print's preliminary rescaling of `a = x̃ - ỹ` into the subbase is not
needed, since the decompositions `a = wₙ - zₙ` are small anyway). -/
theorem isPreBaseNorm : V.IsPreBaseNorm := by
  intro a ha
  have hlt : ∀ n : ℕ, V.bnorm a < (1 / 2) ^ (n + 3) := fun n => by rw [ha]; positivity
  choose w z hw hz hwz hsmall using fun n => OVSt.exists_lt_of_bnorm_lt (hlt n)
  have hw1 : ∀ n, V.tr (w n) ≤ (1 / 2) ^ (n + 2) := fun n => by
    have := hsmall n; have := V.tr_nonneg (hz n)
    have : ((1 : ℝ) / 2) ^ (n + 3) ≤ (1 / 2) ^ (n + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hz1 : ∀ n, V.tr (z n) ≤ (1 / 2) ^ (n + 2) := fun n => by
    have := hsmall n; have := V.tr_nonneg (hw n)
    have : ((1 : ℝ) / 2) ^ (n + 3) ≤ (1 / 2) ^ (n + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hw1' : ∀ n, V.tr (w (n + 1)) ≤ (1 / 2) ^ (n + 2) := fun n =>
    (hw1 (n + 1)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hz1' : ∀ n, V.tr (z (n + 1)) ≤ (1 / 2) ^ (n + 2) := fun n =>
    (hz1 (n + 1)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hle1 : ∀ n, ((1 : ℝ) / 2) ^ (n + 2) ≤ 1 / 4 := fun n => by
    calc ((1 : ℝ) / 2) ^ (n + 2) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have rel : ∀ n, z n + w (n + 1) = z (n + 1) + w n := fun n => by
    have := (hwz n).symm.trans (hwz (n + 1))
    rw [sub_eq_sub_iff_add_eq_add] at this
    rw [add_comm (z n), ← this, add_comm]
  -- the elements of `X`
  let Zs : ℕ → X.carrier := fun n => E.ofVec (z n) (hz n) ((hz1 n).trans (by linarith [hle1 n]))
  let Ws : ℕ → X.carrier := fun n => E.ofVec (w n) (hw n) ((hw1 n).trans (by linarith [hle1 n]))
  have hPtr : ∀ n, V.tr (z n + w (n + 1)) ≤ 1 := fun n => by
    rw [map_add]; linarith [hz1 n, hw1' n, hle1 n]
  let P : ℕ → X.carrier := fun n => E.ofVec (z n + w (n + 1)) (add_nonneg (hz n) (hw (n + 1)))
    (hPtr n)
  have hP1 : ∀ n, SigmaPAM.SumsTo ![Zs n, Ws (n + 1)] (P n) := fun n => by
    refine (E.pair _ _ _).2 ⟨?_, ?_⟩
    · simp only [Zs, Ws, e_ofVec]; rw [← map_add]; exact hPtr n
    · simp only [Zs, Ws, P, e_ofVec]
  have hP2 : ∀ n, SigmaPAM.SumsTo ![Zs (n + 1), Ws n] (P n) := fun n => by
    refine (E.pair _ _ _).2 ⟨?_, ?_⟩
    · simp only [Zs, Ws, e_ofVec]; rw [← map_add, ← rel]; exact hPtr n
    · simp only [Zs, Ws, P, e_ofVec]; exact rel n
  -- the four partial families
  obtain ⟨a₁, ha₁, ta₁⟩ := E.sumsTo_of_small z hz hz1
  obtain ⟨b₁, hb₁, tb₁⟩ := E.sumsTo_of_small (fun n => w (n + 1)) (fun n => hw (n + 1)) hw1'
  obtain ⟨a₂, ha₂, ta₂⟩ := E.sumsTo_of_small (fun n => z (n + 1)) (fun n => hz (n + 1)) hz1'
  obtain ⟨b₂, hb₂, tb₂⟩ := E.sumsTo_of_small w hw hw1
  have pair_of : ∀ p q : X.carrier, V.tr (E.e p).1 ≤ 1 / 2 → V.tr (E.e q).1 ≤ 1 / 2 →
      ∃ c, SigmaPAM.SumsTo ![p, q] c := fun p q hp hq => by
    have htr : V.tr ((E.e p).1 + (E.e q).1) ≤ 1 := by rw [map_add]; linarith
    refine ⟨E.ofVec _ (add_nonneg (E.e p).2.1 (E.e q).2.1) htr, (E.pair _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [← map_add]; exact htr
    · rw [e_ofVec]
  obtain ⟨U, hU⟩ := pair_of a₁ b₁ ta₁ tb₁
  obtain ⟨U', hU'⟩ := pair_of a₂ b₂ ta₂ tb₂
  have hA : SigmaPAM.SumsTo (Sum.elim Zs (fun n => Ws (n + 1))) U :=
    (SigmaPAM.sumsTo_sum_iff _ _ _).2 ⟨a₁, b₁, ha₁, hb₁, hU⟩
  have hB : SigmaPAM.SumsTo (Sum.elim (fun n => Zs (n + 1)) Ws) U' :=
    (SigmaPAM.sumsTo_sum_iff _ _ _).2 ⟨a₂, b₂, ha₂, hb₂, hU'⟩
  have hUU : U = U' :=
    ((CW.sumsTo_pairs _ _ P hP1 U).1 hA).unique ((CW.sumsTo_pairs _ _ P hP2 U').1 hB)
  -- split off `z₀` and `w₀`
  obtain ⟨a', ha', ha'1⟩ := (SigmaPAM.sumsTo_nat_succ_iff Zs a₁).1 ha₁
  obtain ⟨b', hb', hb'1⟩ := (SigmaPAM.sumsTo_nat_succ_iff Ws b₂).1 hb₂
  have ea : a' = a₂ := ha'.unique ha₂
  have eb : b' = b₁ := hb'.unique hb₁
  subst ea; subst eb
  have v1 := ((E.pair _ _ _).1 hU).2
  have v2 := ((E.pair _ _ _).1 hU').2
  have v3 := ((E.pair _ _ _).1 ha'1).2
  have v4 := ((E.pair _ _ _).1 hb'1).2
  rw [hUU, v2, v4] at v1
  rw [v3] at v1
  have hz0 : (E.e (Zs 0)).1 = z 0 := e_ofVec _ _ _ _
  have hw0 : (E.e (Ws 0)).1 = w 0 := e_ofVec _ _ _ _
  rw [hz0] at v1; rw [hw0] at v1
  have : w 0 = z 0 := by
    first
    | linear_combination (norm := module) v1
    | linear_combination (norm := module) -v1
  rw [hwz 0, this, sub_self]

include E in
/-- **SIG 73**, completeness: `V` is complete in the base norm (proof as
printed: absolutely convergent series converge, via the second claim; we run
the argument on a fast Cauchy subsequence). -/
theorem bnComplete : V.BNComplete := by
  intro s hs
  choose Nf hNf using fun k : ℕ => hs ((1 / 2) ^ (k + 3)) (by positivity)
  let n : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), Nf i
  have hnk : ∀ k, Nf k ≤ n k := fun k =>
    Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hnmono : Monotone n := fun i j hij =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hij))
  have hx : ∀ k, V.bnorm (s (n (k + 1)) - s (n k)) < (1 / 2) ^ (k + 3) := fun k =>
    hNf k _ ((hnk k).trans (hnmono (Nat.le_succ k))) _ (hnk k)
  choose y z hy hz hyz hsmall using fun k => OVSt.exists_lt_of_bnorm_lt (hx k)
  have hy1 : ∀ k, V.tr (y k) ≤ (1 / 2) ^ (k + 2) := fun k => by
    have := hsmall k; have := V.tr_nonneg (hz k)
    have : ((1 : ℝ) / 2) ^ (k + 3) ≤ (1 / 2) ^ (k + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hz1 : ∀ k, V.tr (z k) ≤ (1 / 2) ^ (k + 2) := fun k => by
    have := hsmall k; have := V.tr_nonneg (hy k)
    have : ((1 : ℝ) / 2) ^ (k + 3) ≤ (1 / 2) ^ (k + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  obtain ⟨a, ha, -⟩ := E.sumsTo_of_small y hy hy1
  obtain ⟨b, hb, -⟩ := E.sumsTo_of_small z hz hz1
  have sa := E.seriesTo ha
  have sb := E.seriesTo hb
  simp only [e_ofVec] at sa sb
  refine ⟨s (n 0) + (E.e a).1 - (E.e b).1, fun ε hε => ?_⟩
  obtain ⟨Ka, hKa⟩ := sa (ε / 3) (by positivity)
  obtain ⟨Kb, hKb⟩ := sb (ε / 3) (by positivity)
  obtain ⟨Kc, hKc⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 3 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set K := max (max Ka Kb) Kc
  refine ⟨n K, fun m hm => ?_⟩
  have htel : s (n K) - s (n 0) = ∑ k ∈ Finset.range K, (y k - z k) := by
    rw [← Finset.sum_congr rfl (fun k _ => hyz k)]
    exact (Finset.sum_range_sub (fun k => s (n k)) K).symm
  have h1 : V.bnorm (s m - s (n K)) < ε / 3 := by
    have := hNf K m ((hnk K).trans hm) (n K) (hnk K)
    have hp : ((1 : ℝ) / 2) ^ (K + 3) ≤ (1 / 2) ^ Kc :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have h2 : V.bnorm (s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1)) < 2 * (ε / 3) := by
    have e : s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1)
        = ((∑ k ∈ Finset.range K, y k) - (E.e a).1)
          - ((∑ k ∈ Finset.range K, z k) - (E.e b).1) := by
      rw [show s (n K) = s (n 0) + (s (n K) - s (n 0)) by abel, htel, Finset.sum_sub_distrib]
      abel
    rw [e]
    have hadd := OVSt.bnorm_add_le (V := V) ((∑ k ∈ Finset.range K, y k) - (E.e a).1)
      (-((∑ k ∈ Finset.range K, z k) - (E.e b).1))
    rw [← sub_eq_add_neg, OVSt.bnorm_neg] at hadd
    refine lt_of_le_of_lt hadd ?_
    have := hKa K (le_trans (le_max_left _ _) (le_max_left _ _))
    have := hKb K (le_trans (le_max_right _ _) (le_max_left _ _))
    linarith
  calc V.bnorm (s m - (s (n 0) + (E.e a).1 - (E.e b).1))
      = V.bnorm ((s m - s (n K)) + (s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1))) := by
        congr 1; abel
    _ ≤ _ := OVSt.bnorm_add_le _ _
    _ < ε / 3 + 2 * (ε / 3) := by linarith
    _ = ε := by ring

/-- **SIG 73** (`lem:bbns-if-subbase-sigma-wmod`, main.tex:3318, Lemma): let
`V` be an ordered vector space with trace whose subbase carries a (cancellative)
σ-weight `[0,1]`-module structure `X` extending its weight-module structure.
Then `V` is a Banach pre-base-norm space, and for every summable sequence in
`X` the series converges in the base norm to its σ-sum.  (The cancellation
step of the print's proof is done on vectors, where it is automatic.) -/
theorem sig73 :
    V.IsBanachPBN ∧ ∀ (x : ℕ → X.carrier) (s : X.carrier), SigmaPAM.SumsTo x s →
      V.SeriesTo (fun n => (E.e (x n)).1) (E.e s).1 :=
  ⟨⟨isPreBaseNorm E, bnComplete E⟩, fun _ _ h => E.seriesTo h⟩

end SigmaExtension


/-! ## SIG 57, 59: `sBBNS`, and the σ-weight module of its subbases -/

/-- **SIG 57** (main.tex:1639, Definition, text): the category `sBBNS`: Banach
pre-base-norm spaces with a σ-closed subbase, a full subcategory of `OVSt`. -/
structure SBBNS : Type 1 where
  toOVSt : OVSt
  banach : toOVSt.IsBanachPBN
  sigma : toOVSt.SigmaClosedSubbase

namespace SBBNS

instance : Category SBBNS where
  Hom V W := V.toOVSt ⟶ W.toOVSt
  id V := 𝟙 V.toOVSt
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion `sBBNS ↪ OVSt`. -/
def incl : SBBNS ⥤ OVSt where
  obj V := V.toOVSt
  map f := f

instance : incl.Full := ⟨fun f => ⟨f, rfl⟩⟩
instance : incl.Faithful := ⟨fun h => h⟩

variable (V : SBBNS)

/-- The base norm, as a `Norm`. -/
noncomputable abbrev normI : Norm V.toOVSt.carrier := ⟨V.toOVSt.bnorm⟩

theorem core : @NormedSpace.Core ℝ V.toOVSt.carrier _ _ _ (normI V) := by
  letI := normI V
  exact
    { norm_nonneg := OVSt.bnorm_nonneg
      norm_smul := fun c x => by
        show V.toOVSt.bnorm (c • x) = ‖c‖ * V.toOVSt.bnorm x
        rw [OVSt.bnorm_smul, Real.norm_eq_abs]
      norm_triangle := OVSt.bnorm_add_le
      norm_eq_zero_iff := fun x => ⟨V.banach.1 x, fun h => h ▸ OVSt.bnorm_zero⟩ }

/-- The base norm makes `V` a normed space. -/
noncomputable abbrev nag : NormedAddCommGroup V.toOVSt.carrier :=
  letI := normI V
  NormedAddCommGroup.ofCore (core V)

noncomputable abbrev nsp : @NormedSpace ℝ V.toOVSt.carrier _ (nag V).toSeminormedAddCommGroup :=
  letI := nag V
  NormedSpace.ofCore (core V)

attribute [local instance] nag nsp

theorem norm_eq (x : V.toOVSt.carrier) : ‖x‖ = V.toOVSt.bnorm x := rfl

instance complete : CompleteSpace V.toOVSt.carrier := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨v, hv⟩ := V.banach.2 u (fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    exact ⟨N, fun m hm n hn => by
      have := hN m hm n hn; rwa [dist_eq_norm, norm_eq] at this⟩)
  exact ⟨v, Metric.tendsto_atTop.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hv ε hε
    exact ⟨N, fun n hn => by rw [dist_eq_norm, norm_eq]; exact hN n hn⟩⟩

/-- The trace as a continuous linear functional (`|τ x| ≤ ‖x‖`). -/
noncomputable def trL : V.toOVSt.carrier →L[ℝ] ℝ :=
  LinearMap.mkContinuous V.toOVSt.tr 1 fun x => by
    rw [one_mul, Real.norm_eq_abs, norm_eq]; exact OVSt.abs_tr_le x

theorem trL_apply (x : V.toOVSt.carrier) : trL V x = V.toOVSt.tr x :=
  LinearMap.mkContinuous_apply _ _ _ x

/-- `SeriesTo` is convergence of partial sums in the norm topology. -/
theorem seriesTo_iff (x : ℕ → V.toOVSt.carrier) (v : V.toOVSt.carrier) :
    V.toOVSt.SeriesTo x v ↔
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, x i) Filter.atTop (nhds v) := by
  rw [Metric.tendsto_atTop]
  refine forall₂_congr fun ε _ => exists_congr fun N => forall₂_congr fun n _ => ?_
  rw [dist_eq_norm, norm_eq]
  try exact Iff.rfl

variable {V}

/-- Summability for the subbase: finite partial traces are `≤ 1`. -/
def SSummable {J : Type} (x : J → SubB V.toOVSt) : Prop :=
  ∀ F : Finset J, ∑ j ∈ F, V.toOVSt.tr (x j).1 ≤ 1

theorem SSummable.real {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    Summable fun j => V.toOVSt.tr (x j).1 :=
  summable_of_sum_le (fun j => SubB.tr_nonneg (x j)) h

theorem SSummable.vec {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    Summable fun j => (x j).1 := by
  refine Summable.of_norm ?_
  simp only [norm_eq, OVSt.bnorm_of_nonneg (x _).2.1]
  exact h.real

theorem SSummable.tr_tsum {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    V.toOVSt.tr (∑' j, (x j).1) = ∑' j, V.toOVSt.tr (x j).1 := by
  rw [← trL_apply, (trL V).map_tsum h.vec]; simp only [trL_apply]

theorem SSummable.tr_le {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    V.toOVSt.tr (∑' j, (x j).1) ≤ 1 := by
  rw [h.tr_tsum]; exact tsum_le_of_sum_le' zero_le_one h

/-- The sum of a summable family is again positive: the σ-closed subbase. -/
theorem SSummable.nonneg {J : Type} [Countable J] {x : J → SubB V.toOVSt} (h : SSummable x) :
    0 ≤ ∑' j, (x j).1 := by
  rcases finite_or_infinite J with hJ | hJ
  · haveI := Fintype.ofFinite J
    rw [tsum_fintype]; exact Finset.sum_nonneg fun j _ => (x j).2.1
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := J)
    obtain ⟨v, hv0, -, hv⟩ := V.sigma (fun n => (x (e n)).1) (fun n => (x (e n)).2.1)
      (fun N => by
        have := h ((Finset.range N).map e.toEmbedding)
        rwa [Finset.sum_map] at this)
    have hs : HasSum (fun n => (x (e n)).1) (∑' j, (x j).1) :=
      (e.hasSum_iff (f := fun j => (x j).1)).2 h.vec.hasSum
    have := tendsto_nhds_unique hs.tendsto_sum_nat ((seriesTo_iff V _ _).1 hv)
    rw [this]; exact hv0

/-- The σ-sum of the subbase. -/
noncomputable def ssum {J : Type} [Countable J] (x : J → SubB V.toOVSt) (h : SSummable x) :
    SubB V.toOVSt :=
  ⟨∑' j, (x j).1, h.nonneg, h.tr_le⟩

theorem fibre_ssummable {J K : Type} {x : J → SubB V.toOVSt} (h : SSummable x) (p : J → K)
    (k : K) : SSummable (fun j : {j // p j = k} => x j.1) := fun F => by
  have := h (F.map (Function.Embedding.subtype _))
  rwa [Finset.sum_map] at this

theorem hasSum_fibre {J K : Type} {x : J → SubB V.toOVSt} (h : SSummable x) (p : J → K)
    {f : J → ℝ} (hf : HasSum f (∑' j, f j)) (hfs : Summable f) :
    HasSum (fun k => ∑' j : {j // p j = k}, f j.1) (∑' j, f j) := by
  have h1 : HasSum (f ∘ Equiv.sigmaFiberEquiv p) (∑' j, f j) :=
    ((Equiv.sigmaFiberEquiv p).hasSum_iff).2 hf
  exact h1.sigma fun k => (hfs.subtype _).hasSum

/-- The σ-PAM of the subbase of `V ∈ sBBNS`: summable iff the traces sum to
at most `1`, the sum being the sum of the series (in the base norm). -/
noncomputable instance spam (V : SBBNS) : SigmaPAM (SubB V.toOVSt) where
  Summable x := SSummable x
  sum x h := ssum x h
  nonempty := ⟨0⟩
  summable_iff_partition x p := by
    constructor
    · intro h
      refine ⟨fibre_ssummable h p, fun G => ?_⟩
      have hr := h.real
      have hK := hasSum_fibre h p hr.hasSum hr
      simp only [ssum]
      simp only [(fibre_ssummable h p _).tr_tsum]
      refine le_trans (sum_le_hasSum G (fun k _ => tsum_nonneg fun j => SubB.tr_nonneg _) hK) ?_
      exact tsum_le_of_sum_le' zero_le_one h
    · rintro ⟨hk, hK⟩ F
      classical
      rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := F.image p)
        (fun j hj => Finset.mem_image_of_mem p hj)]
      refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hK (F.image p))
      simp only [ssum]
      rw [(hk k).tr_tsum]
      have := sum_le_hasSum ((F.filter fun j => p j = k).subtype fun j => p j = k)
        (fun j _ => SubB.tr_nonneg (x j.1)) (hk k).real.hasSum
      refine le_trans (le_of_eq ?_) this
      have e := Finset.sum_map ((F.filter fun j => p j = k).subtype fun j => p j = k)
        (Function.Embedding.subtype fun j => p j = k) (fun j => V.toOVSt.tr (x j).1)
      rw [Finset.subtype_map, Finset.filter_filter] at e
      exact Eq.trans (Finset.sum_congr (by ext j; simp) (fun _ _ => rfl)) (e.trans rfl)
  sum_partition x p hx h h' := by
    refine SubB.ext ?_
    show ∑' j, (x j).1 = ∑' k, (ssum (fun j : {j // p j = k} => x j.1) (h k)).1
    have h1 : HasSum ((fun j => (x j).1) ∘ Equiv.sigmaFiberEquiv p) (∑' j, (x j).1) :=
      ((Equiv.sigmaFiberEquiv p).hasSum_iff).2 hx.vec.hasSum
    exact (h1.sigma fun k => (h k).vec.hasSum).tsum_eq.symm
  summable_unique x F := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      fun j _ _ => SubB.tr_nonneg (x j)) ?_
    rw [Fintype.sum_unique]; exact (x default).2.2
  sum_unique x h := SubB.ext (by
    show ∑' j, (x j).1 = (x default).1
    rw [tsum_fintype, Fintype.sum_unique])
  limit x h F := by
    have := h F Finset.univ
    rwa [Finset.sum_coe_sort F (fun j => V.toOVSt.tr (x j).1)] at this

theorem sumsTo_iff {J : Type} [Countable J] (x : J → SubB V.toOVSt) (s : SubB V.toOVSt) :
    SigmaPAM.SumsTo x s ↔ SSummable x ∧ HasSum (fun j => (x j).1) s.1 := by
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, h.vec.hasSum⟩
  · rintro ⟨h, hs⟩; exact ⟨h, SubB.ext hs.tsum_eq⟩

theorem zero_eq : (SigmaPAM.zero : SubB V.toOVSt) = 0 :=
  SubB.ext (by
    show ∑' j : Empty, (Empty.elim j : SubB V.toOVSt).1 = 0
    exact tsum_empty)

theorem sumsTo_pair_iff (a b s : SubB V.toOVSt) :
    SigmaPAM.SumsTo ![a, b] s ↔ V.toOVSt.tr a.1 + V.toOVSt.tr b.1 ≤ 1 ∧ s.1 = a.1 + b.1 := by
  rw [sumsTo_iff]
  have hfin : ∀ F : Finset (Fin 2), ∑ j ∈ F, V.toOVSt.tr (![a, b] j).1 ≤
      V.toOVSt.tr a.1 + V.toOVSt.tr b.1 := fun F => by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      fun j _ _ => SubB.tr_nonneg _) ?_
    rw [Fin.sum_univ_two]; rfl
  constructor
  · rintro ⟨h, hs⟩
    refine ⟨?_, ?_⟩
    · have := h Finset.univ; rwa [Fin.sum_univ_two] at this
    · rw [← hs.tsum_eq, tsum_fintype, Fin.sum_univ_two]; rfl
  · rintro ⟨h, hs⟩
    refine ⟨fun F => (hfin F).trans h, ?_⟩
    rw [hs]
    convert hasSum_fintype (fun j : Fin 2 => (![a, b] j).1) using 1
    rw [Fin.sum_univ_two]; rfl

/-- **SIG 59** (proof, main.tex:3434): the subbase of `V ∈ sBBNS` is a σ-weight
`[0,1]`-module, whose countable addition is given by sums of series. -/
noncomputable abbrev sigmaObj (V : SBBNS) : SWMod I where
  carrier := SubB V.toOVSt
  pam := spam V
  act := inferInstance
  weight := wt
  one_smul := WeightMod.one_smul
  mul_smul := WeightMod.mul_smul
  smul_left x J _ r s h := by
    rw [sumsTo_iff]
    have hr := CW.hasSum_of_isCSum h
    have hc := (CW.csummable_I_iff r).1 h.1
    refine ⟨fun F => ?_, ?_⟩
    · simp only [SubB.smul_val, map_smul, smul_eq_mul]
      rw [← Finset.sum_mul]
      exact le_trans (mul_le_of_le_one_right (Finset.sum_nonneg fun j _ => (r j).2.1) x.2.2)
        (hc F)
    · simp only [SubB.smul_val]
      exact hr.smul_const x.1
  smul_right r J _ x s h := by
    rw [sumsTo_iff] at h ⊢
    refine ⟨fun F => ?_, ?_⟩
    · simp only [SubB.smul_val, map_smul, smul_eq_mul]
      rw [← Finset.mul_sum]
      exact le_trans (mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => SubB.tr_nonneg _)
        r.2.2) (h.1 F)
    · simp only [SubB.smul_val]
      exact h.2.const_smul (r : ℝ)
  weight_sumsTo x s h := by
    rw [sumsTo_iff] at h
    refine CW.isCSum_of_hasSum ?_
    simp only [SubB.wt_val]
    exact (trL V).hasSum h.2
  weight_smul := WeightMod.wt_smul
  eq_zero_of_weight x h := by rw [zero_eq]; exact WeightMod.eq_zero_of_wt x h
  summable_of_weight x h := by
    show SSummable x
    intro F
    have := (CW.csummable_I_iff _).1 h F
    simpa only [SubB.wt_val] using this

end SBBNS


namespace SBBNS

attribute [local instance] nag nsp

theorem bnorm_map_le {V W : OVSt} (f : V ⟶ W) (x : V.carrier) :
    W.bnorm (f.toLin x) ≤ V.bnorm x :=
  OVSt.le_bnorm fun a b ha hb h => by
    have := OVSt.bnorm_le (x := f.toLin x) (f.pos a ha) (f.pos b hb) (by rw [h, map_sub])
    linarith [f.tr_le a ha, f.tr_le b hb]

/-- A morphism of `sBBNS` is bounded (norm-decreasing), hence continuous. -/
noncomputable def mapL {V W : SBBNS} (f : V ⟶ W) :
    V.toOVSt.carrier →L[ℝ] W.toOVSt.carrier :=
  LinearMap.mkContinuous f.toLin 1 fun x => by
    rw [one_mul, norm_eq, norm_eq]; exact bnorm_map_le f x

theorem mapL_apply {V W : SBBNS} (f : V ⟶ W) (x : V.toOVSt.carrier) : mapL f x = f.toLin x :=
  LinearMap.mkContinuous_apply _ _ _ x

/-- **SIG 59** (main.tex:1650, and its proof main.tex:3434): the functor
`sBase : sBBNS → sWMod[[0,1]]`, the subbase with sums of series. -/
noncomputable abbrev sBaseS : SBBNS ⥤ SWMod I where
  obj V := sigmaObj V
  map {V W} f :=
    { toFun := fun x => ⟨f.toLin x.1, f.pos _ x.2.1, (f.tr_le _ x.2.1).trans x.2.2⟩
      sigma := fun x s h => by
        rw [sumsTo_iff] at h ⊢
        refine ⟨fun F => le_trans (Finset.sum_le_sum fun j _ => f.tr_le _ (x j).2.1) (h.1 F), ?_⟩
        have := (mapL f).hasSum h.2
        simp only [mapL_apply] at this
        exact this
      map_smul := fun r x => SubB.ext (map_smul f.toLin (r : ℝ) x.1)
      weight_le := fun x => unitInterval_le_iff.2 (f.tr_le _ x.2.1) }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem sBaseS_map_apply {V W : SBBNS} (f : V ⟶ W) (x : SubB V.toOVSt) :
    ((sBaseS.map f).toFun x).1 = f.toLin x.1 := rfl

instance sBaseS_faithful : sBaseS.Faithful where
  map_injective {V W} f g h := by
    refine OVSt.hom_ext fun x => ?_
    have := OVSt.linear_ext_subB (F := f.toLin) (G := g.toLin) fun a => by
      have := congrArg (fun φ : sBaseS.obj V ⟶ sBaseS.obj W => (φ.toFun a).1) h
      simpa [sBaseS_map_apply] using this
    rw [this]

/-- A morphism of σ-weight modules between subbases is a morphism of the
underlying (finite) weight modules. -/
noncomputable def toCW {V W : SBBNS} (φ : sBaseS.obj V ⟶ sBaseS.obj W) :
    sBase.obj V.toOVSt ⟶ sBase.obj W.toOVSt where
  toFun := φ.toFun
  additive := by
    refine ⟨?_, fun {a b} h => ?_⟩
    · have := φ.map_zero
      rw [zero_eq (V := V), zero_eq (V := W)] at this
      exact this
    · have hs : SigmaPAM.SumsTo ![a, b] (ovee a b h) := (sumsTo_pair_iff _ _ _).2 ⟨h, rfl⟩
      have := φ.sigma _ _ hs
      have e : (fun j => φ.toFun (![a, b] j)) = ![φ.toFun a, φ.toFun b] := by
        funext j; fin_cases j <;> rfl
      rw [e, sumsTo_pair_iff] at this
      exact ⟨this.1, SubB.ext this.2.symm⟩
  map_smul := φ.map_smul
  wt_le x := unitInterval_le_iff.1 (φ.weight_le x)

instance sBaseS_full : sBaseS.Full where
  map_surjective {V W} φ := by
    refine ⟨cwExtHom (toCW φ), SWMod.hom_ext fun a => ?_⟩
    have := congrArg (fun ψ : sBase.obj V.toOVSt ⟶ sBase.obj W.toOVSt => ψ.toFun a)
      (sBase_map_extHom (toCW φ))
    exact SubB.ext (congrArg Subtype.val this)

theorem sBaseS_cancellative (V : SBBNS) : (sBaseS.obj V).IsCancellative := by
  intro x y z s hy hz
  rw [sumsTo_pair_iff] at hy hz
  exact SubB.ext (add_left_cancel (hy.2.symm.trans hz.2))

end SBBNS

/-- **SIG 57** (main.tex:1643, Definition, text): the category `sCWMod[[0,1]]` of
cancellative σ-weight `[0,1]`-modules, a full subcategory of `sWMod[[0,1]]`. -/
structure SCWMod : Type 1 where
  toSWMod : SWMod I
  cancel : toSWMod.IsCancellative

namespace SCWMod

noncomputable instance : Category SCWMod where
  Hom X Y := X.toSWMod ⟶ Y.toSWMod
  id X := 𝟙 X.toSWMod
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion `sCWMod ↪ sWMod`. -/
noncomputable def incl : SCWMod ⥤ SWMod I where
  obj X := X.toSWMod
  map f := f

instance : incl.Full := ⟨fun f => ⟨f, rfl⟩⟩
instance : incl.Faithful := ⟨fun h => h⟩

end SCWMod

/-! ### The inverse construction for SIG 59 -/

namespace SWMod

variable (X : SWMod I)

/-- The finite weight-module structure underlying a σ-weight `[0,1]`-module
(its PCM is the one derived from its σ-PAM). -/
noncomputable def wmodOf : @WeightMod X.carrier SigmaPAM.toPCM :=
  letI : PCM X.carrier := SigmaPAM.toPCM
  { toSMul := X.act
    wt := X.weight
    mul_smul := X.mul_smul
    one_smul := X.one_smul
    smul_perp := fun l {a b} h => by
      have := X.smul_right l ![a, b] _ ((SigmaPAM.toPCM_sumsTo_iff a b _).1 ⟨h, rfl⟩)
      have e : (fun j => l • ![a, b] j) = ![l • a, l • b] := by funext j; fin_cases j <;> rfl
      rw [e] at this
      exact (SigmaPAM.toPCM_sumsTo_iff _ _ _).2 this
    perp_smul := fun {l m} h a => by
      have := X.smul_left a ![l, m] _ ((isCSum_pair_iff l m _).2 ⟨h, rfl⟩)
      have e : (fun j => ![l, m] j • a) = ![l • a, m • a] := by funext j; fin_cases j <;> rfl
      rw [e] at this
      exact (SigmaPAM.toPCM_sumsTo_iff _ _ _).2 this
    smul_zero := fun l => X.smul_zero l
    zero_smul := fun a => by
      have := X.smul_left a (Empty.elim : Empty → I) 0 (isCSum_of_isEmpty _)
      exact this.unique (SigmaPAM.sumsTo_of_isEmpty _)
    wt_zero := X.weight_zero
    wt_ovee := fun {a b} h => by
      have := X.weight_sumsTo ![a, b] _ ((SigmaPAM.toPCM_sumsTo_iff a b _).1 ⟨h, rfl⟩)
      have e : (fun j => X.weight (![a, b] j)) = ![X.weight a, X.weight b] := by
        funext j; fin_cases j <;> rfl
      rw [e, isCSum_pair_iff] at this
      obtain ⟨hp, hs⟩ := this
      rw [← hs, GP.I_coe_ovee]
    wt_smul := X.weight_smul
    eq_zero_of_wt := X.eq_zero_of_weight
    perp_of_wt := fun {a b} h => by
      refine X.summable_of_weight ![a, b] ((CW.csummable_I_iff _).2 fun F => ?_)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        fun j _ _ => (X.weight _).2.1) ?_
      rw [Fin.sum_univ_two]; exact h }

/-- The cancellative (finite) weight module of a cancellative σ-weight
module. -/
noncomputable def toCW (hX : X.IsCancellative) : CWMod :=
  @CWMod.mk X.carrier SigmaPAM.toPCM (wmodOf X) (by
    letI : PCM X.carrier := SigmaPAM.toPCM
    intro x y z hy hz h
    exact hX x y z _ ((SigmaPAM.toPCM_sumsTo_iff _ _ _).1 ⟨hy, rfl⟩)
      ((SigmaPAM.toPCM_sumsTo_iff _ _ _).1 ⟨hz, h.symm⟩))

end SWMod

section EssS

variable (X : SWMod I) (hX : X.IsCancellative)

/-- The bijection `X ≃ sBase V(X)`. -/
noncomputable def cwEquiv : X.carrier ≃ SubB (vOf (X.toCW hX)) where
  toFun := (toVOf (X.toCW hX)).toFun
  invFun := (fromVOf (X.toCW hX)).toFun
  left_inv a := congrArg (fun φ : X.toCW hX ⟶ X.toCW hX => φ.toFun a) (vOfIso (X.toCW hX)).inv_hom_id
  right_inv x := congrArg (fun φ : sBase.obj (vOf (X.toCW hX)) ⟶ sBase.obj (vOf (X.toCW hX)) =>
    φ.toFun x) (vOfIso (X.toCW hX)).hom_inv_id

/-- `X` is a σ-structure on `sBase V(X)` extending its weight-module
structure. -/
noncomputable def cwExt : SigmaExtension (vOf (X.toCW hX)) X where
  e := cwEquiv X hX
  map_smul r a := (toVOf (X.toCW hX)).map_smul r a
  wt_eq a := (CW.tr_gmap (X := (X.toCW hX).carrier) a).symm
  pair x y s := by
    constructor
    · rintro ⟨hp, hs⟩
      obtain ⟨h', e⟩ := (toVOf (X.toCW hX)).additive.2 (hp : @Perp (X.toCW hX).carrier _ x y)
      refine ⟨h', ?_⟩
      have e' := congrArg Subtype.val e
      subst hs
      exact e'.symm
    · rintro ⟨h1, h2⟩
      have hp := (@CW.gmap_perp_iff (X.toCW hX).carrier _ _ ⟨(X.toCW hX).cancel⟩ x y).2 h1
      refine ⟨hp, ?_⟩
      refine (cwEquiv X hX).injective (SubB.ext ?_)
      show @CW.gmap (X.toCW hX).carrier _ _ ⟨(X.toCW hX).cancel⟩
        (@ovee (X.toCW hX).carrier _ x y hp) = _
      rw [CW.gmap_ovee hp]; exact h2.symm

theorem cw_sigmaClosed : (vOf (X.toCW hX)).SigmaClosedSubbase := by
  intro y hy hsum
  have hy1 : ∀ n, (vOf (X.toCW hX)).tr (y n) ≤ 1 := fun n => by
    have := hsum (n + 1)
    rw [Finset.sum_range_succ] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) =>
      (vOf (X.toCW hX)).tr_nonneg (hy i)]
  let E := cwExt X hX
  let xs : ℕ → X.carrier := fun n => E.ofVec (y n) (hy n) (hy1 n)
  have hs : SigmaPAM.Summable xs := X.summable_of_weight xs ((CW.csummable_I_iff _).2 fun F => by
    obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range F
    simp only [xs, E.wt_eq, SigmaExtension.e_ofVec]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hM
      fun i _ _ => (vOf (X.toCW hX)).tr_nonneg (hy i)) (hsum M))
  refine ⟨(E.e (SigmaPAM.sum xs hs)).1, (E.e _).2.1, (E.e _).2.2, ?_⟩
  have := E.seriesTo (SigmaPAM.sumsTo_sum hs)
  simpa only [xs, SigmaExtension.e_ofVec] using this

/-- The object `V(X)` of `sBBNS`. -/
noncomputable def sbbnsOf : SBBNS :=
  ⟨vOf (X.toCW hX), ((cwExt X hX).sig73).1, cw_sigmaClosed X hX⟩

attribute [local instance] SBBNS.nag SBBNS.nsp

/-- `cwEquiv`, with codomain the subbase of `V(X) ∈ sBBNS`. -/
noncomputable def cwEquivS : X.carrier ≃ SubB (sbbnsOf X hX).toOVSt := cwEquiv X hX

theorem cwEquivS_tr (a : X.carrier) :
    (sbbnsOf X hX).toOVSt.tr (cwEquivS X hX a).1 = X.weight a :=
  ((cwExt X hX).wt_eq a).symm

theorem cwEquivS_smul (r : I) (a : X.carrier) :
    cwEquivS X hX (r • a) = r • cwEquivS X hX a :=
  (cwExt X hX).map_smul r a

theorem cw_sumsTo {J : Type} [Countable J] {x : J → X.carrier} {s : X.carrier}
    (h : SigmaPAM.SumsTo x s) :
    @SigmaPAM.SumsTo (SubB (sbbnsOf X hX).toOVSt) (SBBNS.spam _) J _
      (fun j => cwEquivS X hX (x j)) (cwEquivS X hX s) := by
  let V := sbbnsOf X hX
  let E := cwExt X hX
  have hss : SBBNS.SSummable (V := V) fun j => cwEquivS X hX (x j) := fun F => by
    have := (CW.csummable_I_iff _).1 (X.weight_sumsTo x s h).1 F
    simpa only [← cwEquivS_tr X hX] using this
  refine (SBBNS.sumsTo_iff (V := V) _ _).2 ⟨hss, ?_⟩
  have hS := (SBBNS.SSummable.vec hss).hasSum
  rcases finite_or_infinite J with hJ | hJ
  · haveI := Fintype.ofFinite J
    have e := (Fintype.equivFin J).symm
    have h' : SigmaPAM.SumsTo (x ∘ e) s := (SigmaPAM.sumsTo_comp_equiv e x s).2 h
    have hfs : ((cwEquivS X hX s).1 : V.toOVSt.carrier)
        = ∑ i, ((cwEquivS X hX (x (e i))).1 : V.toOVSt.carrier) := E.fin_sum _ _ s h'
    rw [hfs, Equiv.sum_comp e (fun j => ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier))]
    exact hasSum_fintype _
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := J)
    have h' : SigmaPAM.SumsTo (x ∘ e) s := (SigmaPAM.sumsTo_comp_equiv e x s).2 h
    have hser := (SBBNS.seriesTo_iff V _ _).1 (E.seriesTo h')
    have hS' : HasSum (fun n => ((cwEquivS X hX (x (e n))).1 : V.toOVSt.carrier))
        (∑' j, ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier)) :=
      (e.hasSum_iff (f := fun j => ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier))).2 hS
    have := tendsto_nhds_unique hS'.tendsto_sum_nat hser
    rw [this] at hS
    exact hS

/-- `sBase V(X) ≅ X` in `sWMod[[0,1]]`. -/
noncomputable def sbbnsIso : SBBNS.sBaseS.obj (sbbnsOf X hX) ≅ X where
  hom :=
    { toFun := (cwEquivS X hX).symm
      sigma := fun y t h => by
        have h0 := (SBBNS.sumsTo_iff (V := sbbnsOf X hX) y t).1 h
        have hs : SigmaPAM.Summable (fun j => (cwEquivS X hX).symm (y j)) :=
          X.summable_of_weight _ ((CW.csummable_I_iff _).2 fun F => by
            have := h0.1 F
            simpa only [← cwEquivS_tr X hX, Equiv.apply_symm_apply] using this)
        have h2 := (SBBNS.sumsTo_iff (V := sbbnsOf X hX) _ _).1
          (cw_sumsTo X hX (SigmaPAM.sumsTo_sum hs))
        simp only [Equiv.apply_symm_apply] at h2
        have ht := h2.2.unique h0.2
        have : SigmaPAM.sum _ hs = (cwEquivS X hX).symm t := by
          rw [Equiv.eq_symm_apply]; exact SubB.ext ht
        rw [← this]; exact SigmaPAM.sumsTo_sum hs
      map_smul := fun r y => (cwEquivS X hX).symm_apply_eq.2
        ((cwEquivS_smul X hX r _).trans
          (congrArg (fun z => r • z) ((cwEquivS X hX).apply_symm_apply y))).symm
      weight_le := fun y => by
        have h1 := cwEquivS_tr X hX ((cwEquivS X hX).symm y)
        rw [Equiv.apply_symm_apply] at h1
        exact unitInterval_le_iff.2 (le_of_eq (h1.symm.trans rfl)) }
  inv :=
    { toFun := cwEquivS X hX
      sigma := fun x s h => cw_sumsTo X hX h
      map_smul := cwEquivS_smul X hX
      weight_le := fun x => unitInterval_le_iff.2 (le_of_eq ((cwEquivS_tr X hX x).trans rfl)) }
  hom_inv_id := SWMod.hom_ext fun y => (cwEquivS X hX).apply_symm_apply y
  inv_hom_id := SWMod.hom_ext fun x => (cwEquivS X hX).symm_apply_apply x

end EssS

/-- **SIG 59** (`prop:sBBNS-equiv-sCWMod`, main.tex:1650, Proposition): the
functor `sBase : sBBNS → sCWMod[[0,1]]`, landing in the cancellative σ-weight
modules. -/
noncomputable def sBaseC : SBBNS ⥤ SCWMod where
  obj V := ⟨SBBNS.sBaseS.obj V, SBBNS.sBaseS_cancellative V⟩
  map f := SBBNS.sBaseS.map f
  map_id V := SBBNS.sBaseS.map_id V
  map_comp f g := SBBNS.sBaseS.map_comp f g

instance : sBaseC.Faithful := ⟨fun h => SBBNS.sBaseS.map_injective h⟩
instance : sBaseC.Full := ⟨fun f => SBBNS.sBaseS.map_surjective (X := _) (Y := _) f⟩
instance : sBaseC.EssSurj := ⟨fun X => ⟨sbbnsOf X.toSWMod X.cancel,
  ⟨{ hom := (sbbnsIso X.toSWMod X.cancel).hom, inv := (sbbnsIso X.toSWMod X.cancel).inv,
     hom_inv_id := (sbbnsIso X.toSWMod X.cancel).hom_inv_id,
     inv_hom_id := (sbbnsIso X.toSWMod X.cancel).inv_hom_id }⟩⟩⟩

/-- **SIG 59** (`prop:sBBNS-equiv-sCWMod`, main.tex:1650, Proposition): there
is an equivalence of categories `sBBNS ≃ sCWMod[[0,1]]`.  Proof as printed:
the subbase of `V ∈ sBBNS` is a σ-weight module under sums of series
(`SBBNS.sigmaObj`); conversely, for a cancellative σ-weight module `X`, SIG 73
makes `V(X)` of SIG 58 a Banach pre-base-norm space with a σ-closed subbase,
and the σ-sums of `X` are the sums of series (`cw_hasSum`); fullness is
SIG 58's extension, which is automatically σ-normal. -/
instance sBaseC_isEquivalence : sBaseC.IsEquivalence where

/-- For theorem 60: the essential image of `sBase : sBBNS → sWMod[[0,1]]` is
the cancellative modules. -/
theorem sBaseS_essImage (X : SWMod I) (hX : X.IsCancellative) :
    ∃ V : SBBNS, Nonempty (SBBNS.sBaseS.obj V ≅ X) :=
  ⟨sbbnsOf X hX, ⟨sbbnsIso X hX⟩⟩

/-- The unit object `[0,1]` of `sWMod[[0,1]]` is cancellative. -/
theorem SWMod.unit_isCancellative (hM : IsSigmaEffectMonoid I) :
    (SWMod.unit I hM).IsCancellative := by
  intro x y z s hy hz
  have hy' := (canonical_sumsTo_iff hM.1 _ _).1 hy
  have hz' := (canonical_sumsTo_iff hM.1 _ _).1 hz
  obtain ⟨hpy, ey⟩ := (isCSum_pair_iff x y s).1 hy'
  obtain ⟨hpz, ez⟩ := (isCSum_pair_iff x z s).1 hz'
  have e1 := (GP.I_coe_ovee hpy).symm.trans (congrArg Subtype.val ey)
  have e2 := (GP.I_coe_ovee hpz).symm.trans (congrArg Subtype.val ez)
  exact Subtype.ext (by linarith)

/-- Countable coproducts of cancellative σ-weight modules are cancellative. -/
theorem SWMod.coprod_isCancellative {M : Type} [EffectMonoid M] [Fact (IsSigmaEffectMonoid M)]
    {Λ : Type} [Countable Λ] (X : Λ → SWMod M) (h : ∀ l, (X l).IsCancellative) :
    (SWMod.coprod X).IsCancellative := by
  intro x y z s hy hz
  have hy' := (SWMod.coprod_sumsTo_iff X _ _).1 hy
  have hz' := (SWMod.coprod_sumsTo_iff X _ _).1 hz
  refine Subtype.ext (funext fun l => h l (x.1 l) (y.1 l) (z.1 l) (s.1 l) ?_ ?_)
  · refine (SigmaPAM.sumsTo_congr fun j => ?_).1 (hy' l); fin_cases j <;> rfl
  · refine (SigmaPAM.sumsTo_congr fun j => ?_).1 (hz' l); fin_cases j <;> rfl


/-! ## `sBBNS` is a σ-effectus -/

section SBBNSEffectus

open SigmaPAM

instance fact_unitInterval_sigma : Fact (IsSigmaEffectMonoid I) :=
  ⟨unitInterval_isSigmaEffectMonoid⟩

/-- The essential image of `sBase : sBBNS → sWMod[[0,1]]` (the cancellative
modules, SIG 59) is closed under countable coproducts. -/
theorem sbbns_hcop (J : Type) [Countable J] (X : J → SBBNS) :
    ∃ Y : SBBNS, Nonempty (SBBNS.sBaseS.obj Y ≅ ∐ fun j => SBBNS.sBaseS.obj (X j)) := by
  obtain ⟨Y, ⟨e⟩⟩ := sBaseS_essImage (SWMod.coprod fun j => SBBNS.sBaseS.obj (X j))
    (SWMod.coprod_isCancellative _ fun j => SBBNS.sBaseS_cancellative (X j))
  exact ⟨Y, ⟨e ≪≫ (SWMod.coprodIsoC _).symm⟩⟩

/-- `sBBNS` has countable coproducts (SIG 59: those of `sWMod[[0,1]]`). -/
instance : HasCountableCoproducts SBBNS :=
  hasCountableCoproducts_of_ff SBBNS.sBaseS sbbns_hcop

/-- The hom-sets of `sBBNS` as σ-PAMs, transported along SIG 59. -/
noncomputable instance sbbnsHomPAM (X Y : SBBNS) : SigmaPAM (X ⟶ Y) :=
  SigmaPAM.ofEquiv ((Functor.FullyFaithful.ofFullyFaithful SBBNS.sBaseS).homEquiv)

theorem sbbns_sumsCompatible : SumsCompatible SBBNS.sBaseS :=
  fun x s => SigmaPAM.ofEquiv_sumsTo_iff _ x s

/-- The unit object of `sBBNS` (a base-norm space with subbase `[0,1]`). -/
noncomputable def sbbnsUnit : SBBNS :=
  (sBaseS_essImage (SWMod.unit I unitInterval_isSigmaEffectMonoid)
    (SWMod.unit_isCancellative _)).choose

noncomputable def sbbnsUnitIso :
    SBBNS.sBaseS.obj sbbnsUnit ≅ SigmaEffectus.«I» (C := SWMod I) :=
  (sBaseS_essImage (SWMod.unit I unitInterval_isSigmaEffectMonoid)
    (SWMod.unit_isCancellative _)).choose_spec.some

/-- **SIG 59** (main.tex:1653): "As `sCWMod[[0,1]]` is a full subcategory of
`sWMod[[0,1]]`, it is a σ-effectus, and hence so is `sBBNS`": the structure
transported along the fully faithful `sBase : sBBNS → sWMod[[0,1]]`. -/
noncomputable instance sbbns_sigmaEffectus : SigmaEffectus SBBNS :=
  sbbns_sumsCompatible.sigmaEffectus sbbnsUnit sbbnsUnitIso
    (preserves_of_ff SBBNS.sBaseS sbbns_hcop)

/-- `sBase : sBBNS → sWMod[[0,1]]` is a morphism of σ-effectuses. -/
noncomputable def sbbnsMorphism : SigmaEffectusMorphism SBBNS (SWMod I) :=
  sbbns_sumsCompatible.morphism sbbnsUnit sbbnsUnitIso
    (preserves_of_ff SBBNS.sBaseS sbbns_hcop)

end SBBNSEffectus

/-! ## SIG 60, SIG 61: the probabilistic case, states -/

section SIG60

variable {C : Type} [Category.{0} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- **SIG 60** (`thm:convex-effectus-embedding-2`, main.tex:1659, Theorem): a
state-separated σ-effectus with scalars `[0,1]` whose substates are
cancellative has a faithful morphism of σ-effectuses `G : C → sBBNS`, with
`sSt(A) ≅ sBase(GA)` (as σ-weight modules over `C(I,I)ᵒᵖ`, acting on
`sBase(GA)` through the isomorphism).  Proof as printed: SIG 37 and SIG 67
(`sSt` is a morphism of σ-effectuses, faithful since state separation is
substate separation under normalisation, SIG 39, and `[0,1]` has no zero
divisors, SIG 40) and SIG 59.  Stated for a small `C` (`C : Type`), the
universe of `sBBNS`. -/
theorem sig60 (hsep : StateSeparated C) (φ : EffectMonoidHom (Scal C) I)
    (ψ : EffectMonoidHom I (Scal C)) (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a)
    (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) (hcanc : ∀ A : C, (sStObj A).IsCancellative) :
    ∃ (G : SigmaEffectusMorphism C SBBNS) (hφ : IsSigmaAdditiveC (emHomToMOp φ).toFun)
      (hψ : IsSigmaAdditiveC (emHomFromMOp ψ).toFun), G.F.Faithful ∧
      ∀ A : C, Nonempty (sStObj A ≅ restrictSWObj (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ
        (SBBNS.sBaseS.obj (G.F.obj A))) := by
  have hφ : IsSigmaAdditiveC (emHomToMOp φ).toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive (emHomToMOp φ))
      (emHom_isAdditive (emHomFromMOp ψ)) hψφ hφψ
  have hψ : IsSigmaAdditiveC (emHomFromMOp ψ).toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive (emHomFromMOp ψ))
      (emHom_isAdditive (emHomToMOp φ)) hφψ hψφ
  let B := restrictSWMorphism (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ
  let G := sigmaMorphismComp sbbnsMorphism B
  have := restrictSWFunctor_full (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ
  have : G.F.Full := by
    show (SBBNS.sBaseS ⋙ restrictSWFunctor _ hφ _ hψ hψφ hφψ).Full
    infer_instance
  have := restrictSWFunctor_faithful (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ
  have := SBBNS.sBaseS_faithful
  have : G.F.Faithful := by
    show (SBBNS.sBaseS ⋙ restrictSWFunctor _ hφ _ hψ hψφ hφψ).Faithful
    infer_instance
  let Φ := sStMorphism (C := C)
  have h : ∀ A : C, ∃ Y : SBBNS, Nonempty (G.F.obj Y ≅ Φ.F.obj A) := by
    intro A
    obtain ⟨Y, ⟨e⟩⟩ := sBaseS_essImage
      (restrictSWObj (emHomFromMOp ψ) hψ (emHomToMOp φ) hφ hφψ hψφ (sStObj A)) (hcanc A)
    exact ⟨Y, ⟨(restrictSWFunctor (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ).mapIso e ≪≫
      restrictSWRoundTrip (emHomToMOp φ) hφ (emHomFromMOp ψ) hψ hψφ hφψ (sStObj A)⟩⟩
  have hN : AdmitsNormalisation C :=
    admitsNormalisation_of_noZeroDivisors
      (EMIso.noZeroDivisors ⟨φ, ψ, hψφ, hφψ⟩ emNoZeroDivisors_unitInterval)
  have hsst : (sStFunctor (C := C)).Faithful :=
    substateSeparated_iff_faithful.1 ((stateSeparated_iff_substateSeparated hN).1 hsep)
  refine ⟨liftMorphism G Φ h, hφ, hψ, ?_, fun A => ?_⟩
  · have : Φ.F.Faithful := hsst
    exact liftMorphism_faithful G Φ h
  · exact ⟨((liftIso G Φ h).app A).symm⟩

end SIG60

section SIG61

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- **SIG 61** (main.tex:1667, Remark), first sentence: in a
predicate-separated σ-effectus the substates are cancellative.  No printed
proof; ours: `ω ⊕ ω₁ = ω ⊕ ω₂` gives `p∘ω ⊕ p∘ω₁ = p∘ω ⊕ p∘ω₂` for every
predicate `p`, so `p∘ω₁ = p∘ω₂` by cancellation in the effect algebra of
scalars, and `ω₁ = ω₂` by predicate separation. -/
theorem sig61_cancellative (hsep : PredicateSeparated C) (A : C) :
    (sStObj A).IsCancellative := by
  intro ω ω₁ ω₂ s h1 h2
  refine hsep ω₁ ω₂ fun p => ?_
  have k1 := comp_sumsTo_left p h1
  have k2 := comp_sumsTo_left p h2
  have e1 : (fun j => ![ω, ω₁] j ≫ p) = ![ω ≫ p, ω₁ ≫ p] := by funext i; fin_cases i <;> rfl
  have e2 : (fun j => ![ω, ω₂] j ≫ p) = ![ω ≫ p, ω₂ ≫ p] := by funext i; fin_cases i <;> rfl
  rw [e1] at k1
  rw [e2] at k2
  have hp1 : Perp (ω ≫ p) (ω₁ ≫ p) := k1.summable
  have hp2 : Perp (ω ≫ p) (ω₂ ≫ p) := k2.summable
  have q1 : ovee (ω ≫ p) (ω₁ ≫ p) hp1 = s ≫ p := k1.sum_eq _
  have q2 : ovee (ω ≫ p) (ω₂ ≫ p) hp2 = s ≫ p := k2.sum_eq _
  refine eabasics_cancellation (PCM.perp_comm hp1) (PCM.perp_comm hp2) ?_
  rw [← PCM.ovee_comm hp1, ← PCM.ovee_comm hp2, q1, q2]

end SIG61

/-- **SIG 61** (main.tex:1667, Remark), second sentence: a state- and
predicate-separated σ-effectus with scalars `[0,1]` embeds (faithful
morphisms of σ-effectuses) into both `sBBNS` and `sBOUSᵒᵖ` (SIG 56, SIG 60
and the first sentence). -/
theorem sig61 {C : Type} [Category.{0} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
    (hstate : StateSeparated C) (hpred : PredicateSeparated C)
    (φ : EffectMonoidHom (Scal C) I) (ψ : EffectMonoidHom I (Scal C))
    (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a) (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) :
    (∃ G : SigmaEffectusMorphism C SBBNS, G.F.Faithful) ∧
      ∃ F : SigmaEffectusMorphism C SBOUSᵒᵖ, F.F.Faithful := by
  obtain ⟨G, -, -, hG, -⟩ := sig60 hstate φ ψ hψφ hφψ (sig61_cancellative hpred)
  obtain ⟨F, -, hF, -⟩ := sig56 hpred φ ψ hψφ hφψ
  exact ⟨⟨G, hG⟩, ⟨F, hF⟩⟩

end Papers.SIG
