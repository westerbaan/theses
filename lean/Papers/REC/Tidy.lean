/-
Papers/REC/Tidy.lean

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707 (2021): the points of §2–§4 left open by the
sessions that wrote `Effectus.lean`, `Algebras.lean` and `Decompose.lean`
(`PLAN.md` §6, "still open in §2–§4"):

* **REC 36** (an irreducible directed-complete effect monoid is `{0}`, `{0,1}`
  or `[0,1]`) is discharged from OAP 71 (`Papers.OAP.oap71_iso`).  OAP 71 is
  stated for effect monoids *without zero divisors*; the bridge is
  `noZeroDivisors_iff_irreducible`: in an ω-complete effect monoid, `a·b = 0`
  gives `a·⌈b⌉ = 0` (OAP 34) with `⌈b⌉` idempotent (OAP 35), and
  irreducibility (REC 20, 21) forces `⌈b⌉ ∈ {0, 1}`.
* **REC 42** (`DCOUS ≃ DCEA_c`): the categories `DCOUSCat` (directed-complete
  order unit spaces in the sense of REC 41, positive linear contractions) and
  `DCEACCat` (`Decompose.lean`), the unit-interval functor
  `unitIntervalFunctor : DCOUSCat ⥤ DCEACCat`, and the proof that it is an
  equivalence (`rec42`): faithful (an OUS is spanned by its unit interval),
  full (an additive action-preserving map of unit intervals extends to a
  positive linear contraction, `IntervalExt`), essentially surjective (the
  Gudder–Pulmannová space `GP.Vec E` of OAP 62, which is Archimedean and
  directed complete by OAP 59–61).  Wright's lemma (REC 41, last sentence) is
  `rec41_banach`; the DCOUS halves of REC 94, 95, 97 (`rec94_dcous`,
  `rec95_dcousFunctor`, `rec97_unitInterval`) compose with the inverse of REC 42.
* **REC 89**, third bullet (a monoidal effectus has a monoidal Karoubi
  envelope): a symmetric monoidal structure on `Split C` with `(A,t) ⊗ (B,s) =
  (A ⊗ B, t ⊗ s)` and unit `id_I`, and the coherence isomorphisms modified by
  the idempotents as printed (`λ_t = t ∘ λ_A ∘ (t ⊗ id_I)`); `Split C` is then a
  monoidal effectus (`rec89_monoidal`).
-/
import Papers.REC.Decompose
import Papers.REC.Scalars
import Papers.OAP.Main

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
open CategoryTheory.Limits hiding HasImages
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v

/-! ## REC 36: irreducible directed-complete effect monoids -/

section REC36

open scoped Papers.OAP

variable {M : Type u} [EffectMonoid M]

/-- The bridge between REC 36 and OAP 71: an ω-complete effect monoid is
irreducible (REC 20) iff it has no non-trivial zero divisors.  `⇒`: if
`a·b = 0` then `a·⌈b⌉ = 0` (OAP 34), and `⌈b⌉` is an idempotent (OAP 35), so
`⌈b⌉ = 0` — whence `b ≤ ⌈b⌉ = 0` — or `⌈b⌉ = 1` — whence `a = a·1 = 0`
(REC 21: irreducible iff the only idempotents are `0`, `1`).  `⇐`: an
idempotent `p` has `p·p^⊥ = 0` (OAP 18). -/
theorem noZeroDivisors_iff_irreducible [Papers.OAP.OmegaComplete M] :
    (∀ a b : M, a * b = 0 → a = 0 ∨ b = 0) ↔ IsIrreducible M := by
  rw [rec21_irreducible_iff]
  constructor
  · intro hM p hp
    exact Papers.OAP.idem_eq_zero_or_one hM hp
  · intro hid a b hab
    rcases hid (Papers.OAP.ceil b) (Papers.OAP.ceil_idem b) with h0 | h1
    · right
      exact Papers.OAP.eq_zero_of_le_zero (h0 ▸ Papers.OAP.le_ceil b)
    · left
      have := Papers.OAP.oap34 hab
      rwa [h1, EffectMonoid.mul_one] at this

/-- An effect monoid isomorphism in OAP's form (`EMIsIso`) gives one in REC's
(`EMIso`). -/
noncomputable def emIsoOfIsIso {N : Type v} [EffectMonoid N] {f : EffectMonoidHom M N}
    (hf : Papers.OAP.EMIsIso f) : EMIso M N where
  hom := f
  inv := hf.choose
  inv_hom := hf.choose_spec.1
  hom_inv := hf.choose_spec.2

/-- **REC 36** (short.tex:776, Theorem), for ω-complete effect monoids: an
irreducible ω-complete effect monoid is isomorphic to `{0}`, `{0,1}` or
`[0,1]`.  OAP 71 (`Papers.OAP.oap71_iso`) through the bridge
`noZeroDivisors_iff_irreducible`. -/
theorem rec36_omega [Papers.OAP.OmegaComplete M] (hirr : IsIrreducible M) :
    Subsingleton M ∨ Nonempty (EMIso M Bool) ∨ Nonempty (EMIso M I) := by
  rcases Papers.OAP.oap71_iso.{u, 0} (noZeroDivisors_iff_irreducible.2 hirr) with
    ⟨f, g, hgf, -⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  · left
    exact ⟨fun a b => by rw [← hgf a, ← hgf b]⟩
  · exact Or.inr (Or.inl ⟨emIsoOfIsIso hf⟩)
  · exact Or.inr (Or.inr ⟨emIsoOfIsIso hf⟩)

/-- **REC 36** (short.tex:776, Theorem) **holds**: an irreducible
directed-complete effect monoid is isomorphic (as an effect monoid) to `{0}`,
`{0,1}` or `[0,1]`.  The paper cites OAP; this is OAP 71 (`oap71_iso`) via
`noZeroDivisors_iff_irreducible` (directed completeness gives OAP's
ω-completeness, `oapDirectedComplete_of`). -/
theorem rec36_holds : IrreducibleDCClassification.{u} := by
  intro M _ hdc hirr
  have := oapDirectedComplete_of hdc
  exact rec36_omega hirr

end REC36

/-! ## REC 42: `DCOUS ≃ DCEA_c`

### The order-unit norm (REC 41) -/

section OUSNorm

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- The set whose infimum is the order-unit norm (REC 41). -/
def normSet (v : V) : Set ℝ := {l : ℝ | -(l • ouUnit V) ≤ v ∧ v ≤ l • ouUnit V}

theorem ousNorm_eq (v : V) : ousNorm V v = sInf (normSet v) := rfl

theorem normSet_nonempty (v : V) : (normSet v).Nonempty := by
  obtain ⟨n, h1, h2⟩ := Papers.OAP.oap58_orderUnit v
  exact ⟨n, h1, h2⟩

/-- A negative bound forces the order unit, hence the space, to be zero. -/
theorem unit_eq_zero_of_neg {v : V} {l : ℝ} (hl : l < 0) (h : l ∈ normSet v) :
    ouUnit V = 0 := by
  have h1 : -(l • ouUnit V) ≤ l • ouUnit V := h.1.trans h.2
  have h2 : (0 : V) ≤ (-l)⁻¹ • ((2 * l) • ouUnit V) := by
    refine ou_smul_nonneg (inv_nonneg.2 (by linarith)) ?_
    have : (2 * l) • ouUnit V = l • ouUnit V - -(l • ouUnit V) := by
      rw [sub_neg_eq_add, ← add_smul]; ring_nf
    rw [this]; exact sub_nonneg.2 h1
  have e : (-l)⁻¹ • ((2 * l) • ouUnit V) = -(2 : ℝ) • ouUnit V := by
    have hl0 : l ≠ 0 := hl.ne
    rw [_root_.smul_smul]; congr 1; field_simp
  rw [e, neg_smul, neg_nonneg] at h2
  have h3 : ouUnit V ≤ 0 := by
    have := ou_smul_le_smul (show (0 : ℝ) ≤ 1 / 2 by norm_num) h2
    rwa [_root_.smul_smul, smul_zero, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at this
  exact le_antisymm h3 ou_unit_nonneg

theorem eq_zero_of_unit_eq_zero (h : ouUnit V = 0) (v : V) : v = 0 := by
  obtain ⟨n, h1, h2⟩ := Papers.OAP.oap58_orderUnit v
  simp only [h, smul_zero, neg_zero] at h1 h2
  exact le_antisymm h2 h1

/-- `‖v‖ ≤ l` whenever `l ≥ 0` bounds `v`. -/
theorem ousNorm_le {v : V} {l : ℝ} (hl : 0 ≤ l) (h1 : -(l • ouUnit V) ≤ v)
    (h2 : v ≤ l • ouUnit V) : ousNorm V v ≤ l := by
  rw [ousNorm_eq]
  by_cases hb : BddBelow (normSet v)
  · exact csInf_le hb ⟨h1, h2⟩
  · rw [Real.sInf_of_not_bddBelow hb]; exact hl

/-- If `‖v‖ < c`, some bound `l < c` of `v` exists. -/
theorem exists_bound_of_ousNorm_lt {v : V} {c : ℝ} (h : ousNorm V v < c) :
    ∃ l, l < c ∧ -(l • ouUnit V) ≤ v ∧ v ≤ l • ouUnit V := by
  rw [ousNorm_eq] at h
  by_cases hb : BddBelow (normSet v)
  · obtain ⟨l, hl, hlc⟩ := exists_lt_of_csInf_lt (normSet_nonempty v) h
    exact ⟨l, hlc, hl⟩
  · obtain ⟨l, hl, hlc⟩ := not_bddBelow_iff.1 hb c
    exact ⟨l, hlc, hl⟩

theorem ousNorm_nonneg (v : V) : 0 ≤ ousNorm V v := by
  by_contra hneg
  push Not at hneg
  obtain ⟨l, hl, h1, h2⟩ := exists_bound_of_ousNorm_lt hneg
  have hu := unit_eq_zero_of_neg hl ⟨h1, h2⟩
  have hnb : ¬ BddBelow (normSet v) := by
    rw [not_bddBelow_iff]
    intro x
    refine ⟨x - 1, ?_, by linarith⟩
    show -((x - 1) • ouUnit V) ≤ v ∧ v ≤ (x - 1) • ouUnit V
    rw [hu, eq_zero_of_unit_eq_zero hu v, smul_zero, neg_zero]
    exact ⟨le_rfl, le_rfl⟩
  rw [ousNorm_eq, Real.sInf_of_not_bddBelow hnb] at hneg
  exact lt_irrefl _ hneg

theorem ousNorm_unit_le : ousNorm V (ouUnit V) ≤ 1 :=
  ousNorm_le zero_le_one (by rw [one_smul]; exact neg_le_self ou_unit_nonneg)
    (by rw [one_smul])

/-- A REC 41 order unit space is Archimedean: `v ≤ ε·1` for all `ε > 0`
gives `v ≤ 0`, by closedness of the cone applied to `-v`. -/
theorem archimedean_of_isOUS [IsOUS V] : OUSArchimedean V := by
  intro v hv
  have : 0 ≤ -v := IsOUS.cone_closed (-v) fun ε hε => by
    refine ⟨(ε / 2) • ouUnit V - v, sub_nonneg.2 (hv _ (by positivity)), ?_⟩
    have e : -v - ((ε / 2) • ouUnit V - v) = -((ε / 2) • ouUnit V) := by abel
    rw [e]
    refine lt_of_le_of_lt (ousNorm_le (l := ε / 2) (by positivity) le_rfl ?_) (by linarith)
    exact (neg_nonpos.2 (ou_smul_unit_nonneg (by positivity))).trans
      (ou_smul_unit_nonneg (by positivity))
  exact neg_nonneg.1 this

/-- Conversely an Archimedean order unit space (in the tree's sense) satisfies
REC 41: the seminorm is a norm and the cone is closed. -/
theorem isOUS_of_archimedean (hA : OUSArchimedean V) : IsOUS V where
  norm_eq_zero v hv := by
    have hb : ∀ ε : ℝ, 0 < ε → v ≤ ε • ouUnit V ∧ -v ≤ ε • ouUnit V := fun ε hε => by
      obtain ⟨l, hl, h1, h2⟩ := exists_bound_of_ousNorm_lt (v := v) (c := ε) (by rw [hv]; exact hε)
      exact ⟨h2.trans (ou_smul_unit_mono hl.le), (neg_le.1 h1).trans (ou_smul_unit_mono hl.le)⟩
    exact le_antisymm (hA v fun ε hε => (hb ε hε).1)
      (neg_nonpos.1 (hA (-v) fun ε hε => (hb ε hε).2))
  cone_closed v hv := by
    refine neg_nonpos.1 (hA (-v) fun ε hε => ?_)
    obtain ⟨w, hw, hn⟩ := hv ε hε
    obtain ⟨l, hl, h1, -⟩ := exists_bound_of_ousNorm_lt hn
    have : -v ≤ l • ouUnit V - w := by
      have := neg_le_neg h1
      rw [neg_neg, neg_sub] at this
      calc -v = (w - v) - w := by abel
        _ ≤ l • ouUnit V - w := sub_le_sub_right this w
    exact this.trans ((sub_le_self _ hw).trans (ou_smul_unit_mono hl.le))

end OUSNorm

section Contraction

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
  {W : Type v} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

/-- A positive linear map between order unit spaces is a contraction for the
order-unit norms iff it is subunital, `f(1) ≤ 1` (the target satisfying
REC 41). -/
theorem contraction_iff_subunital [IsOUS W] (f : V →ₗ[ℝ] W) (hf : ∀ v, 0 ≤ v → 0 ≤ f v) :
    (∀ v, ousNorm W (f v) ≤ ousNorm V v) ↔ f (ouUnit V) ≤ ouUnit W := by
  constructor
  · intro h
    have hn : ousNorm W (f (ouUnit V)) ≤ 1 := (h _).trans ousNorm_unit_le
    have : f (ouUnit V) - ouUnit W ≤ 0 := archimedean_of_isOUS _ fun ε hε => by
      obtain ⟨l, hl, -, h2⟩ := exists_bound_of_ousNorm_lt (v := f (ouUnit V)) (c := 1 + ε)
        (by linarith)
      have := h2.trans (ou_smul_unit_mono hl.le)
      rw [add_smul, one_smul] at this
      exact sub_le_iff_le_add'.2 this
    exact sub_nonpos.1 this
  · intro h1 v
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨l, hl, h1v, h2v⟩ := exists_bound_of_ousNorm_lt (v := v) (c := ousNorm V v + ε)
      (by linarith)
    rcases lt_or_ge l 0 with hl0 | hl0
    · have hu := unit_eq_zero_of_neg hl0 ⟨h1v, h2v⟩
      rw [eq_zero_of_unit_eq_zero hu v, map_zero]
      refine lt_of_le_of_lt (ousNorm_le le_rfl ?_ ?_) (by linarith [ousNorm_nonneg (V := V) 0])
      · rw [zero_smul, neg_zero]
      · rw [zero_smul]
    · refine lt_of_le_of_lt (ousNorm_le hl0 ?_ ?_) hl
      · have := hf _ (sub_nonneg.2 h1v)
        rw [map_sub, map_neg, map_smul] at this
        have h' : -(l • f (ouUnit V)) ≤ f v := sub_nonneg.1 this
        exact (neg_le_neg (ou_smul_le_smul hl0 h1)).trans h'
      · have := hf _ (sub_nonneg.2 h2v)
        rw [map_sub, map_smul] at this
        exact (sub_nonneg.1 this).trans (ou_smul_le_smul hl0 h1)

end Contraction

/-! ### Extending an additive map on the unit interval to a linear map -/

section IntervalExt

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
  {W : Type v} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

/-- The data of an additive, `[0,1]`-homogeneous map `g` on the unit interval
`[0,1]_V`, with values in `[0,1]_W` (only its values on `[0,1]_V` matter). -/
structure IntervalMap (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] (W : Type v) [AddCommGroup W] [Module ℝ W] [PartialOrder W]
    [OrderUnitSpace W] where
  g : V → W
  add : ∀ a b : V, 0 ≤ a → 0 ≤ b → a + b ≤ ouUnit V → g (a + b) = g a + g b
  smul : ∀ (r : ℝ) (a : V), 0 ≤ r → r ≤ 1 → 0 ≤ a → a ≤ ouUnit V → g (r • a) = r • g a
  nonneg : ∀ a : V, 0 ≤ a → a ≤ ouUnit V → 0 ≤ g a

namespace IntervalMap

variable (φ : IntervalMap V W)

theorem g_zero : φ.g 0 = 0 := by
  have := φ.add 0 0 le_rfl le_rfl (by rw [add_zero]; exact ou_unit_nonneg)
  rw [add_zero] at this
  simpa using this

/-- `t • g(t⁻¹ • p)` does not depend on the bound `t` of `p`. -/
theorem scale_eq_of_le {p : V} (hp : 0 ≤ p) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (hpt : p ≤ t • ouUnit V) :
    t' • φ.g (t'⁻¹ • p) = t • φ.g (t⁻¹ • p) := by
  have ht' : 0 < t' := ht.trans_le htt
  have ha0 : 0 ≤ t⁻¹ • p := ou_smul_nonneg (inv_nonneg.2 ht.le) hp
  have ha1 : t⁻¹ • p ≤ ouUnit V := by
    have := ou_smul_le_smul (inv_nonneg.2 ht.le) hpt
    rwa [_root_.smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
  have e : t'⁻¹ • p = (t / t') • (t⁻¹ • p) := by
    rw [_root_.smul_smul]; congr 1; field_simp
  rw [e, φ.smul _ _ (div_nonneg ht.le ht'.le) ((div_le_one ht').2 htt) ha0 ha1, _root_.smul_smul]
  congr 1; field_simp

theorem scale_eq {p : V} (hp : 0 ≤ p) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (hpt : p ≤ t • ouUnit V) (hpt' : p ≤ t' • ouUnit V) :
    t' • φ.g (t'⁻¹ • p) = t • φ.g (t⁻¹ • p) := by
  rcases le_total t t' with h | h
  · exact φ.scale_eq_of_le hp ht h hpt
  · exact (φ.scale_eq_of_le hp ht' h hpt').symm

/-- A positive bound of `p`. -/
noncomputable def bnd (p : V) : ℝ := ((ou_exists_le_smul_unit p).choose : ℝ) + 1

theorem bnd_pos (p : V) : 0 < bnd p := by unfold bnd; positivity

theorem le_bnd (p : V) : p ≤ bnd p • ouUnit V :=
  (ou_exists_le_smul_unit p).choose_spec.trans (ou_smul_unit_mono (by unfold bnd; linarith))

/-- The extension to the positive cone: `gp(p) = t • g(t⁻¹ • p)` for any
bound `t > 0` of `p`. -/
noncomputable def gp (p : V) : W := bnd p • φ.g ((bnd p)⁻¹ • p)

theorem gp_eq {p : V} (hp : 0 ≤ p) {t : ℝ} (ht : 0 < t) (hpt : p ≤ t • ouUnit V) :
    φ.gp p = t • φ.g (t⁻¹ • p) :=
  φ.scale_eq hp ht (bnd_pos p) hpt (le_bnd p)

theorem gp_zero : φ.gp 0 = 0 := by
  rw [φ.gp_eq le_rfl one_pos (by rw [one_smul]; exact ou_unit_nonneg), smul_zero, φ.g_zero,
    smul_zero]

theorem gp_of_le_one {a : V} (h0 : 0 ≤ a) (h1 : a ≤ ouUnit V) : φ.gp a = φ.g a := by
  rw [φ.gp_eq h0 one_pos (by rwa [one_smul]), inv_one, one_smul, one_smul]

theorem gp_add {p q : V} (hp : 0 ≤ p) (hq : 0 ≤ q) : φ.gp (p + q) = φ.gp p + φ.gp q := by
  set t := bnd p + bnd q
  have ht : 0 < t := add_pos (bnd_pos p) (bnd_pos q)
  have hpt : p ≤ t • ouUnit V :=
    (le_bnd p).trans (ou_smul_unit_mono (le_add_of_nonneg_right (bnd_pos q).le))
  have hqt : q ≤ t • ouUnit V :=
    (le_bnd q).trans (ou_smul_unit_mono (le_add_of_nonneg_left (bnd_pos p).le))
  have hpqt : p + q ≤ t • ouUnit V := by
    have := add_le_add (le_bnd p) (le_bnd q)
    rwa [← add_smul] at this
  rw [φ.gp_eq (add_nonneg hp hq) ht hpqt, φ.gp_eq hp ht hpt, φ.gp_eq hq ht hqt, smul_add,
    φ.add _ _ (ou_smul_nonneg (inv_nonneg.2 ht.le) hp) (ou_smul_nonneg (inv_nonneg.2 ht.le) hq),
    smul_add]
  have := ou_smul_le_smul (inv_nonneg.2 ht.le) hpqt
  rwa [_root_.smul_smul, inv_mul_cancel₀ ht.ne', one_smul, smul_add] at this

theorem gp_smul {p : V} (hp : 0 ≤ p) {r : ℝ} (hr : 0 ≤ r) : φ.gp (r • p) = r • φ.gp p := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [zero_smul, zero_smul, gp_zero]
  have ht : 0 < r * bnd p := mul_pos hr (bnd_pos p)
  have hrp : r • p ≤ (r * bnd p) • ouUnit V := by
    rw [mul_smul]; exact ou_smul_le_smul hr.le (le_bnd p)
  have e : (r * bnd p)⁻¹ * r = (bnd p)⁻¹ := by
    have := (bnd_pos p).ne'; have := hr.ne'; field_simp
  rw [φ.gp_eq (ou_smul_nonneg hr.le hp) ht hrp, gp, _root_.smul_smul r (bnd p),
    _root_.smul_smul _ r p, e]

theorem gp_nonneg {p : V} (hp : 0 ≤ p) : 0 ≤ φ.gp p := by
  have ha1 : (bnd p)⁻¹ • p ≤ ouUnit V := by
    have := ou_smul_le_smul (inv_nonneg.2 (bnd_pos p).le) (le_bnd p)
    rwa [_root_.smul_smul, inv_mul_cancel₀ (bnd_pos p).ne', one_smul] at this
  exact ou_smul_nonneg (bnd_pos p).le
    (φ.nonneg _ (ou_smul_nonneg (inv_nonneg.2 (bnd_pos p).le) hp) ha1)

/-- The extension to all of `V`: `F(v) = gp(v + N·1) - gp(N·1)` for a bound
`N` of `-v`. -/
noncomputable def ext (v : V) : W := φ.gp (v + bnd (-v) • ouUnit V) - φ.gp (bnd (-v) • ouUnit V)

/-- `F(p - q) = gp(p) - gp(q)` for positive `p`, `q`: the extension is
well defined on differences. -/
theorem ext_sub {p q : V} (hp : 0 ≤ p) (hq : 0 ≤ q) : φ.ext (p - q) = φ.gp p - φ.gp q := by
  set N := bnd (-(p - q))
  have hN : 0 ≤ N • ouUnit V := ou_smul_unit_nonneg (bnd_pos _).le
  have hP : 0 ≤ p - q + N • ouUnit V := by
    have := sub_nonneg.2 (le_bnd (-(p - q)))
    rwa [sub_neg_eq_add, add_comm] at this
  have e : φ.gp (p - q + N • ouUnit V) + φ.gp q = φ.gp p + φ.gp (N • ouUnit V) := by
    rw [← φ.gp_add hP hq, ← φ.gp_add hp hN]
    congr 1; abel
  unfold ext
  rw [sub_eq_sub_iff_add_eq_add, e]

theorem ext_of_nonneg {p : V} (hp : 0 ≤ p) : φ.ext p = φ.gp p := by
  have := φ.ext_sub hp le_rfl
  rwa [sub_zero, gp_zero, sub_zero] at this

theorem ext_add (v w : V) : φ.ext (v + w) = φ.ext v + φ.ext w := by
  obtain ⟨p, q, hp, hq, rfl⟩ := ou_eq_sub_of_nonneg v
  obtain ⟨p', q', hp', hq', rfl⟩ := ou_eq_sub_of_nonneg w
  have e : p - q + (p' - q') = (p + p') - (q + q') := by abel
  rw [e, φ.ext_sub (add_nonneg hp hp') (add_nonneg hq hq'), φ.ext_sub hp hq, φ.ext_sub hp' hq',
    φ.gp_add hp hp', φ.gp_add hq hq']
  abel

theorem ext_smul (r : ℝ) (v : V) : φ.ext (r • v) = r • φ.ext v := by
  obtain ⟨p, q, hp, hq, rfl⟩ := ou_eq_sub_of_nonneg v
  rcases le_total 0 r with hr | hr
  · rw [smul_sub, φ.ext_sub (ou_smul_nonneg hr hp) (ou_smul_nonneg hr hq), φ.ext_sub hp hq,
      φ.gp_smul hp hr, φ.gp_smul hq hr, smul_sub]
  · have hr' : 0 ≤ -r := neg_nonneg.2 hr
    have e : r • (p - q) = (-r) • q - (-r) • p := by
      rw [neg_smul, neg_smul, sub_neg_eq_add, smul_sub]; abel
    rw [e, φ.ext_sub (ou_smul_nonneg hr' hq) (ou_smul_nonneg hr' hp), φ.ext_sub hp hq,
      φ.gp_smul hq hr', φ.gp_smul hp hr', neg_smul, neg_smul, smul_sub]
    abel

/-- The linear extension. -/
noncomputable def lin : V →ₗ[ℝ] W where
  toFun := φ.ext
  map_add' := φ.ext_add
  map_smul' := φ.ext_smul

theorem lin_apply (v : V) : φ.lin v = φ.ext v := rfl

theorem lin_nonneg {p : V} (hp : 0 ≤ p) : 0 ≤ φ.lin p := by
  rw [lin_apply, φ.ext_of_nonneg hp]; exact φ.gp_nonneg hp

theorem lin_of_mem {a : V} (h0 : 0 ≤ a) (h1 : a ≤ ouUnit V) : φ.lin a = φ.g a := by
  rw [lin_apply, φ.ext_of_nonneg h0, φ.gp_of_le_one h0 h1]

end IntervalMap

/-- Two positive... in fact any two linear maps out of an order unit space
that agree on the unit interval agree everywhere: `V` is spanned by `[0,1]_V`. -/
theorem linearMap_ext_of_interval {f g : V →ₗ[ℝ] W}
    (h : ∀ a : V, 0 ≤ a → a ≤ ouUnit V → f a = g a) : f = g := by
  have hp : ∀ p : V, 0 ≤ p → f p = g p := fun p hp => by
    set t := IntervalMap.bnd p
    have ht := IntervalMap.bnd_pos p
    have e : p = t • (t⁻¹ • p) := by rw [_root_.smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have h1 : t⁻¹ • p ≤ ouUnit V := by
      have := ou_smul_le_smul (inv_nonneg.2 ht.le) (IntervalMap.le_bnd p)
      rwa [_root_.smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
    calc f p = t • f (t⁻¹ • p) := by rw [← map_smul, ← e]
      _ = t • g (t⁻¹ • p) := by rw [h _ (ou_smul_nonneg (inv_nonneg.2 ht.le) hp) h1]
      _ = g p := by rw [← map_smul, ← e]
  ext v
  obtain ⟨p, q, hp', hq', rfl⟩ := ou_eq_sub_of_nonneg v
  rw [map_sub, map_sub, hp p hp', hp q hq']

end IntervalExt

/-! ### The unit interval of an order unit space as a convex effect algebra -/

section UnitInterval

variable (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- The convex structure of `[0,1]_V` (REC 40; OAP's `ousEMod` through the
bridge of REC 39). -/
noncomputable abbrev uiConvex : @ConvexEA (Set.Icc (0 : V) (ouUnit V)) (Papers.OAP.ousEA V) :=
  @ConvexEA.ofEffectModule _ (Papers.OAP.ousEA V) (Papers.OAP.ousEMod V)

variable {V}

theorem ui_le_iff {x y : Set.Icc (0 : V) (ouUnit V)} :
    @PCM.le _ (Papers.OAP.ousEA V).toPCM x y ↔ (x : V) ≤ y :=
  Papers.OAP.oap3_le_iff V (ouUnit V) ou_unit_nonneg x y

variable (V) in
/-- REC 41's directed completeness of `V` is directed completeness (REC 30) of
the effect algebra `[0,1]_V`. -/
theorem ui_directedComplete (h : IsDirectedCompleteOUS V) :
    @DirectedCompleteEA _ (Papers.OAP.ousEA V) := by
  let := Papers.OAP.ousEA V
  intro D hD
  obtain ⟨s, hs, hub, hlub⟩ := h (Subtype.val '' D) (by rintro _ ⟨x, -, rfl⟩; exact x.2) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
    exact ⟨z, ⟨z, hz, rfl⟩, ui_le_iff.1 hxz, ui_le_iff.1 hyz⟩)
  refine ⟨⟨s, hs⟩, fun x hx => ui_le_iff.2 (hub _ ⟨x, hx, rfl⟩), fun u hu => ui_le_iff.2
    (hlub u u.2 ?_)⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ui_le_iff.1 (hu x hx)

end UnitInterval

/-! ### The category DCOUS -/

/-- **REC 41** (short.tex:837, Definition): the objects of **DCOUS**:
directed-complete order unit spaces — ordered real vector spaces with an order
unit (the tree's `OrderUnitSpace`) whose order-unit seminorm is a norm and
whose cone is closed (`IsOUS`), and whose unit interval is directed complete
(`IsDirectedCompleteOUS`). -/
structure DCOUSCat : Type (u + 1) where
  carrier : Type u
  [grp : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [ord : PartialOrder carrier]
  [ous : OrderUnitSpace carrier]
  [isOUS : IsOUS carrier]
  dc : IsDirectedCompleteOUS carrier

attribute [instance] DCOUSCat.grp DCOUSCat.mod DCOUSCat.ord DCOUSCat.ous DCOUSCat.isOUS

/-- **REC 41** (short.tex:837, Definition): the morphisms of **DCOUS**, the
positive linear contractions (for the order-unit norms). -/
@[ext] structure DCOUSHom (V W : DCOUSCat.{u}) where
  toLin : V.carrier →ₗ[ℝ] W.carrier
  pos : ∀ v, 0 ≤ v → 0 ≤ toLin v
  contr : ∀ v, ousNorm W.carrier (toLin v) ≤ ousNorm V.carrier v

/-- **REC 41** (short.tex:837, Definition): the category **DCOUS**. -/
instance : Category DCOUSCat.{u} where
  Hom := DCOUSHom
  id _ := ⟨LinearMap.id, fun _ h => h, fun _ => le_rfl⟩
  comp f g := ⟨g.toLin ∘ₗ f.toLin, fun v h => g.pos _ (f.pos v h),
    fun v => (g.contr _).trans (f.contr v)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem DCOUSHom.subunital {V W : DCOUSCat.{u}} (f : V ⟶ W) :
    f.toLin (ouUnit V.carrier) ≤ ouUnit W.carrier :=
  (contraction_iff_subunital f.toLin f.pos).1 f.contr

theorem DCOUSHom.map_le_one {V W : DCOUSCat.{u}} (f : V ⟶ W) {x : V.carrier}
    (hx : x ≤ ouUnit V.carrier) : f.toLin x ≤ ouUnit W.carrier := by
  have := f.pos _ (sub_nonneg.2 hx)
  rw [map_sub, sub_nonneg] at this
  exact this.trans f.subunital

/-- **REC 41** (short.tex:837, Definition), last sentence (Wright, *Measures
with values in a partially ordered vector space*, Lemma 1.1, cited): a
directed-complete order unit space is Banach.  Via OAP 60 (directed complete
⟺ bounded directed complete) and Wright's argument as formalised for OAP 66
(`Papers.OAP.wright_normComplete`). -/
theorem rec41_banach (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] (h : IsDirectedCompleteOUS V) : IsBanachOUS V := by
  have hdc : Papers.OAP.OUSDirectedComplete V := by
    let := Papers.OAP.ousEA V
    exact ⟨fun S hS => (ui_directedComplete V h S fun x hx y hy => by
      obtain ⟨z, hz, hxz, hyz⟩ := hS.2 x hx y hy
      exact ⟨z, hz, hxz, hyz⟩).imp fun s hs => ⟨hs.1, fun u hu => hs.2 u hu⟩⟩
  have hom : Papers.OAP.OUSOmegaComplete V :=
    @Papers.OAP.DirectedComplete.omegaComplete _ (Papers.OAP.ousEA V) hdc
  have hc := Papers.OAP.wright_normComplete (Papers.OAP.oap60_omega.1 hom)
  intro s hs
  obtain ⟨v, hv⟩ := hc s fun ε hε => by
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    obtain ⟨l, hl, -, h2⟩ := exists_bound_of_ousNorm_lt (hN m hm n hn)
    exact h2.trans (ou_smul_unit_mono hl.le)
  refine ⟨v, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hv (ε / 2) (by positivity)
  refine ⟨N, fun n hn => lt_of_le_of_lt (ousNorm_le (by positivity) ?_ (hN n hn).1) (by linarith)⟩
  have := (hN n hn).2
  rw [neg_le, neg_sub]; exact this

/-! ### The unit-interval functor `DCOUS → DCEA_c` -/

attribute [local instance] Papers.OAP.ousEA uiConvex

/-- `V ↦ [0,1]_V`. -/
noncomputable abbrev uiObj (V : DCOUSCat.{u}) : DCEACCat.{u} :=
  @DCEACCat.mk (Set.Icc (0 : V.carrier) (ouUnit V.carrier)) (Papers.OAP.ousEA V.carrier)
    (uiConvex V.carrier) (ui_directedComplete V.carrier V.dc)

/-- The restriction of a positive linear map `f` with `f(1) ≤ 1` to the unit
intervals, as a morphism of `DCEA_c`. -/
noncomputable def uiHom {V W : DCOUSCat.{u}} (f : V.carrier →ₗ[ℝ] W.carrier)
    (hpos : ∀ v, 0 ≤ v → 0 ≤ f v) (hle : ∀ x, x ≤ ouUnit V.carrier → f x ≤ ouUnit W.carrier) :
    uiObj V ⟶ uiObj W :=
  ⟨{ toFun := fun x => ⟨f x, hpos _ x.2.1, hle _ x.2.2⟩
     perp_map := fun {x y} h => by
       show f x + f y ≤ ouUnit W.carrier
       rw [← map_add]; exact hle _ h
     ovee_map := fun {x y} h => Subtype.ext (map_add f x.1 y.1) },
    fun l x => Subtype.ext (map_smul f (l : ℝ) (x : V.carrier))⟩

theorem uiHom_apply {V W : DCOUSCat.{u}} (f : V.carrier →ₗ[ℝ] W.carrier) (hpos hle)
    (x : (uiObj V).carrier) :
    ((uiHom (V := V) (W := W) f hpos hle).1.toFun x : W.carrier) = f (x : V.carrier) := rfl

/-- The unit-interval functor `DCOUS → DCEA_c`, `V ↦ [0,1]_V`, `f ↦ f|_{[0,1]}`. -/
noncomputable abbrev unitIntervalFunctor : DCOUSCat.{u} ⥤ DCEACCat.{u} where
  obj := uiObj
  map f := uiHom f.toLin f.pos fun _ hx => f.map_le_one hx
  map_id _ := rfl
  map_comp _ _ := Subtype.ext (PCMHom.ext' rfl)

theorem unitIntervalFunctor_map_apply {V W : DCOUSCat.{u}} (f : V ⟶ W)
    (x : (uiObj V).carrier) :
    ((unitIntervalFunctor.map f).1.toFun x : W.carrier) = f.toLin (x : V.carrier) := rfl

/-- The unit-interval functor is faithful: a linear map is determined by its
values on the unit interval. -/
instance : unitIntervalFunctor.{u}.Faithful where
  map_injective {V W} f g h := DCOUSHom.ext (linearMap_ext_of_interval fun a h0 h1 => by
    have := congrArg (fun φ : uiObj V ⟶ uiObj W => (φ.1.toFun ⟨a, h0, h1⟩ : W.carrier)) h
    exact this)

/-- An additive action-preserving map of unit intervals as an `IntervalMap`. -/
noncomputable def toIntervalMap {V W : DCOUSCat.{u}} (φ : uiObj V ⟶ uiObj W) :
    IntervalMap V.carrier W.carrier := by
  classical
  exact
  { g := fun v => if h : v ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier)
      then ((φ.1.toFun ⟨v, h⟩ : (uiObj W).carrier) : W.carrier) else 0
    add := fun a b ha hb hab => by
      have hma : a ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier) :=
        ⟨ha, (le_add_of_nonneg_right hb).trans hab⟩
      have hmb : b ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier) :=
        ⟨hb, (le_add_of_nonneg_left ha).trans hab⟩
      have hmab : a + b ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier) := ⟨add_nonneg ha hb, hab⟩
      rw [dite_eq_left hma, dite_eq_left hmb, dite_eq_left hmab]
      have hp : @Perp _ (Papers.OAP.ousEA V.carrier).toPCM ⟨a, hma⟩ ⟨b, hmb⟩ := hab
      have e := φ.1.ovee_map hp
      have e' : (⟨a + b, hmab⟩ : Set.Icc (0 : V.carrier) (ouUnit V.carrier)) =
          @ovee _ (Papers.OAP.ousEA V.carrier).toPCM ⟨a, hma⟩ ⟨b, hmb⟩ hp := Subtype.ext rfl
      rw [e', e]
      rfl
    smul := fun r a hr0 hr1 ha0 ha1 => by
      have hma : a ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier) := ⟨ha0, ha1⟩
      have hmra : r • a ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier) :=
        ⟨ou_smul_nonneg hr0 ha0, by
          have := ou_smul_le_smul hr0 ha1
          exact this.trans (by
            have := ou_smul_unit_mono (X := V.carrier) hr1
            rwa [one_smul] at this)⟩
      rw [dite_eq_left hma, dite_eq_left hmra]
      have e := φ.2 ⟨r, hr0, hr1⟩ ⟨a, hma⟩
      have e' : (⟨r • a, hmra⟩ : Set.Icc (0 : V.carrier) (ouUnit V.carrier)) =
          @HSMul.hSMul I _ _ (@instHSMul _ _ (uiConvex V.carrier).toSMul) ⟨r, hr0, hr1⟩
            ⟨a, hma⟩ := Subtype.ext rfl
      rw [e']
      exact congrArg Subtype.val e
    nonneg := fun a h0 h1 => by
      rw [dite_eq_left ⟨h0, h1⟩]
      exact (φ.1.toFun ⟨a, h0, h1⟩).2.1 }

theorem toIntervalMap_g {V W : DCOUSCat.{u}} (φ : uiObj V ⟶ uiObj W) {a : V.carrier}
    (h : a ∈ Set.Icc (0 : V.carrier) (ouUnit V.carrier)) :
    (toIntervalMap φ).g a = ((φ.1.toFun ⟨a, h⟩ : (uiObj W).carrier) : W.carrier) := by
  unfold toIntervalMap
  simp only
  rw [dite_eq_left h]

/-- The unit-interval functor is full: an additive, action-preserving map of
unit intervals extends (uniquely) to a positive linear map (`IntervalMap.lin`),
which is subunital, hence a contraction (`contraction_iff_subunital`). -/
instance : unitIntervalFunctor.{u}.Full where
  map_surjective {V W} φ := by
    let ψ := toIntervalMap φ
    have h1 : ψ.lin (ouUnit V.carrier) ≤ ouUnit W.carrier := by
      rw [ψ.lin_of_mem ou_unit_nonneg le_rfl, toIntervalMap_g φ ⟨ou_unit_nonneg, le_rfl⟩]
      exact (φ.1.toFun _).2.2
    refine ⟨⟨ψ.lin, fun _ h => ψ.lin_nonneg h,
      (contraction_iff_subunital ψ.lin fun _ h => ψ.lin_nonneg h).2 h1⟩, ?_⟩
    refine Subtype.ext (PCMHom.ext' (funext fun x => Subtype.ext ?_))
    show ψ.lin (x : V.carrier) = ((φ.1.toFun x : (uiObj W).carrier) : W.carrier)
    rw [ψ.lin_of_mem x.2.1 x.2.2, toIntervalMap_g φ x.2]

/-! ### Essential surjectivity: the Gudder–Pulmannová space -/

section GPObj

variable (E : DCEACCat.{u})

/-- The Gudder–Pulmannová order unit space `GP.Vec E` of a directed-complete
convex effect algebra (OAP 62) is a directed-complete order unit space in the
sense of REC 41: it is Archimedean (OAP 61, `gp_archimedean`), hence its
seminorm is a norm and its cone is closed; it is directed complete
(`gp_directedComplete`). -/
noncomputable abbrev gpObj : DCOUSCat.{u} :=
  letI : EffectModule I E.carrier := ConvexEA.toEffectModule
  haveI : Papers.OAP.DirectedComplete E.carrier := oapDirectedComplete_of E.dc
  { carrier := GP.Vec E.carrier
    ous := Papers.OAP.gpOrderUnitSpace
    isOUS := isOUS_of_archimedean Papers.OAP.gp_archimedean
    dc := fun D hD hd => by
      rcases D.eq_empty_or_nonempty with rfl | hne
      · exact ⟨0, ⟨le_rfl, ou_unit_nonneg⟩, by simp, fun t ht _ => ht.1⟩
      · obtain ⟨u, hu, hub, hlub⟩ :=
          Papers.OAP.ousDirected_iff.1 Papers.OAP.gp_directedComplete D hD hne hd
        exact ⟨u, hu, fun d hdD => hub hdD, fun t ht htD => hlub t ht htD⟩ }

/-- `E ≅ [0,1]_{GP.Vec E}` in `DCEA_c` (OAP 62: `gpEquiv` preserves and
reflects `⊥`, preserves `⊻` and the action). -/
noncomputable def gpIso : unitIntervalFunctor.obj (gpObj E) ≅ E := by
  letI : EffectModule I E.carrier := ConvexEA.toEffectModule
  exact
  { hom := ⟨{ toFun := fun y => (Papers.OAP.gpEquiv E.carrier).symm y
              perp_map := fun {x y} h => by
                refine Papers.OAP.gmap_perp_iff.2 ?_
                have hx := congrArg Subtype.val ((Papers.OAP.gpEquiv E.carrier).apply_symm_apply x)
                have hy := congrArg Subtype.val ((Papers.OAP.gpEquiv E.carrier).apply_symm_apply y)
                simp only [Papers.OAP.gpEquiv_apply] at hx hy
                rw [hx, hy]; exact h
              ovee_map := fun {x y} h => by
                apply (Papers.OAP.gpEquiv E.carrier).injective
                refine Subtype.ext ?_
                rw [Equiv.apply_symm_apply, Papers.OAP.gpEquiv_apply, GP.gmap_ovee]
                have hx := congrArg Subtype.val ((Papers.OAP.gpEquiv E.carrier).apply_symm_apply x)
                have hy := congrArg Subtype.val ((Papers.OAP.gpEquiv E.carrier).apply_symm_apply y)
                simp only [Papers.OAP.gpEquiv_apply] at hx hy
                rw [hx, hy]; rfl },
      fun l x => by
        show (Papers.OAP.gpEquiv E.carrier).symm _ = l • (Papers.OAP.gpEquiv E.carrier).symm x
        apply (Papers.OAP.gpEquiv E.carrier).injective
        refine Subtype.ext ?_
        rw [Equiv.apply_symm_apply, Papers.OAP.gpEquiv_apply]
        erw [GP.gmap_smul]
        have hx := congrArg Subtype.val ((Papers.OAP.gpEquiv E.carrier).apply_symm_apply x)
        simp only [Papers.OAP.gpEquiv_apply] at hx
        rw [hx]; rfl⟩
    inv := ⟨{ toFun := fun a => Papers.OAP.gpEquiv E.carrier a
              perp_map := fun {a b} h => Papers.OAP.gmap_perp_iff.1 h
              ovee_map := fun {a b} h => Subtype.ext (GP.gmap_ovee h) },
      fun l a => Subtype.ext (GP.gmap_smul l a)⟩
    hom_inv_id := Subtype.ext (PCMHom.ext' (funext fun y =>
      (Papers.OAP.gpEquiv E.carrier).apply_symm_apply y))
    inv_hom_id := Subtype.ext (PCMHom.ext' (funext fun a =>
      (Papers.OAP.gpEquiv E.carrier).symm_apply_apply a)) }

end GPObj

instance : unitIntervalFunctor.{u}.EssSurj where
  mem_essImage E := ⟨gpObj E, ⟨gpIso E⟩⟩

instance : unitIntervalFunctor.{u}.IsEquivalence where

/-- **REC 42** (`prop:convex-OUS-equiv`, short.tex:844, Proposition): the
equivalence between ordered vector spaces and convex effect algebras restricts
to an equivalence `DCOUS ≃ DCEA_c`: the unit-interval functor `V ↦ [0,1]_V`
from directed-complete order unit spaces with positive linear contractions to
directed-complete convex effect algebras with additive action-preserving maps
is an equivalence of categories.  The paper cites "cf. SIG Prop. 55" (SIG
proves the σ-version); the proof here: faithful — `V` is spanned by `[0,1]_V`;
full — an additive action-preserving map of unit intervals extends to a
positive linear map (`IntervalMap.lin`), which is subunital, i.e. a contraction
(`contraction_iff_subunital`); essentially surjective — Gudder–Pulmannová
(OAP 62, `gpIso`), `GP.Vec E` being Archimedean and directed complete
(OAP 59–61), hence an object of DCOUS (`gpObj`). -/
noncomputable def rec42 : DCOUSCat.{u} ≌ DCEACCat.{u} := unitIntervalFunctor.asEquivalence

theorem rec42_functor : rec42.{u}.functor = unitIntervalFunctor := rfl

/-! ### The DCOUS halves of REC 94, 95 and 97 -/

section DCOUSHalves

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
  [HasImages C] [HasFilters C] [HasComprehension C] [CompatibleFiltersComprehensions C]

/-- **REC 94** (`prop:effectus-ortho-OUS`, short.tex:1705, Proposition), with
the printed codomain: `Pred` as a functor `C → OAᵒᵖ × DCOUSᵒᵖ` (here
`Cᵒᵖ → OA × DCOUS`), `rec94_functor` composed with the inverse of REC 42. -/
noncomputable def rec94_dcous (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) : Cᵒᵖ ⥤ OACat.{v} × DCOUSCat.{v} :=
  rec94_functor σs hdc hsep ⋙ (𝟭 OACat.{v}).prod rec42.{v}.inverse

/-- **REC 94**: the second component of `rec94_dcous` is a directed-complete
order unit space whose unit interval is `s^⊥ · Pred(A)`, naturally in `A`. -/
noncomputable def rec94_dcous_unitInterval (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) :
    (rec94_dcous σs hdc hsep ⋙ CategoryTheory.Prod.snd _ _) ⋙ unitIntervalFunctor ≅
      rec94_functor σs hdc hsep ⋙ CategoryTheory.Prod.snd _ _ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (rec94_functor σs hdc hsep ⋙ CategoryTheory.Prod.snd _ _)
    rec42.{v}.counitIso ≪≫ Functor.rightUnitor _

/-- **REC 95** (`prop:splits-directed-complete`, short.tex:1720, Proposition),
with the printed codomain: `Pred : C₂ → DCOUSᵒᵖ` (`rec95_dcFunctor` composed
with the inverse of REC 42). -/
noncomputable def rec95_dcousFunctor (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) : (dcSplitting σs hsep).ε'.Partᵒᵖ ⥤ DCOUSCat.{v} :=
  rec95_dcFunctor σs hdc hsep ⋙ rec42.{v}.inverse

/-- **REC 95**: the predicates of an object of `C₂` are the unit interval of
the order unit space `rec95_dcousFunctor`, naturally. -/
noncomputable def rec95_dcous_unitInterval (σs : ScalarSplit C) (hdc : DirectedCompleteEffectus C)
    (hsep : SeparatingStates C) :
    rec95_dcousFunctor σs hdc hsep ⋙ unitIntervalFunctor ≅ rec95_dcFunctor σs hdc hsep :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (rec95_dcFunctor σs hdc hsep) rec42.{v}.counitIso ≪≫
    Functor.rightUnitor _

end DCOUSHalves

/-- **REC 97** (`prop:boolean-and-convex`, short.tex:1786, Proposition), the
parenthetical "more specifically the unit interval of a directed-complete order
unit space": every directed-complete convex effect algebra (such as `A_c` of
`rec97`) is isomorphic in `DCEA_c` to the unit interval `[0,1]_V` of a
directed-complete order unit space `V` (REC 42, `gpIso`). -/
theorem rec97_unitInterval (E : DCEACCat.{u}) :
    ∃ V : DCOUSCat.{u}, Nonempty (unitIntervalFunctor.obj V ≅ E) :=
  ⟨gpObj E, ⟨gpIso E⟩⟩

/-! ## REC 89, third bullet: the Karoubi envelope of a monoidal effectus -/

section SplitMonoidal

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

namespace SplitMon

/-! ### Morphisms of `C` commuting with the idempotents -/

/-- A morphism `sg : A → B` of `C` between the carriers of `(A, t)`, `(B, s)`
commutes with the idempotents: `sg ∘ t = s ∘ sg`. -/
def Eqv {X Y : Split C} (sg : X.obj.X ⟶ Y.obj.X) : Prop := X.obj.p ≫ sg = sg ≫ Y.obj.p

/-- The morphism `s ∘ sg ∘ t : (A, t) → (B, s)` of `Split C`. -/
noncomputable def sw {X Y : Split C} (sg : X.obj.X ⟶ Y.obj.X) : X ⟶ Y :=
  KCat.homMk (X.obj.p ≫ sg ≫ Y.obj.p) (by simp only [Category.assoc, Karoubi.idem,
    Karoubi.idem_assoc])

theorem sw_f {X Y : Split C} (sg : X.obj.X ⟶ Y.obj.X) :
    Karoubi.Hom.f (sw sg) = X.obj.p ≫ sg ≫ Y.obj.p := rfl

theorem homMk_eq_sw {X Y : Split C} (sg : X.obj.X ⟶ Y.obj.X) (h) :
    KCat.homMk (X := X) (Y := Y) sg h = sw sg := KCat.hom_ext h.symm

theorem sw_hom {X Y : Split C} (f : X ⟶ Y) : sw f.f = f := KCat.hom_ext (KCat.comm f)

theorem eqv_hom {X Y : Split C} (f : X ⟶ Y) : Eqv f.f := (KCat.p_comp f).trans (KCat.comp_p f).symm

theorem eqv_p (X : Split C) : Eqv (X := X) (Y := X) X.obj.p := rfl

theorem sw_id (X : Split C) : sw (𝟙 X.obj.X) = 𝟙 X :=
  KCat.hom_ext (by rw [sw_f, Category.id_comp, Karoubi.idem, KCat.id_f])

theorem sw_comp {X Y Z : Split C} {sg : X.obj.X ⟶ Y.obj.X} {tg : Y.obj.X ⟶ Z.obj.X} (h : Eqv sg) :
    sw sg ≫ sw tg = sw (sg ≫ tg) := KCat.hom_ext (by
  rw [KCat.comp_f, sw_f, sw_f, sw_f]
  simp only [Category.assoc, Karoubi.idem_assoc]
  rw [← Category.assoc sg, ← h]
  simp only [Category.assoc, Karoubi.idem_assoc])

theorem Eqv.comp {X Y Z : Split C} {sg : X.obj.X ⟶ Y.obj.X} {tg : Y.obj.X ⟶ Z.obj.X}
    (hsg : Eqv sg) (htg : Eqv tg) : Eqv (sg ≫ tg) := by
  unfold Eqv at *
  rw [← Category.assoc, hsg, Category.assoc, htg, Category.assoc]

theorem Eqv.inv {X Y : Split C} {sg : X.obj.X ≅ Y.obj.X} (h : Eqv sg.hom) : Eqv sg.inv := by
  unfold Eqv at *
  calc Y.obj.p ≫ sg.inv = sg.inv ≫ (sg.hom ≫ Y.obj.p) ≫ sg.inv := by simp
    _ = sg.inv ≫ (X.obj.p ≫ sg.hom) ≫ sg.inv := by rw [h]
    _ = sg.inv ≫ X.obj.p := by simp

/-- An isomorphism of `C` commuting with the idempotents gives one of
`Split C`. -/
noncomputable def swIso {X Y : Split C} (sg : X.obj.X ≅ Y.obj.X) (h : Eqv sg.hom) : X ≅ Y where
  hom := sw sg.hom
  inv := sw sg.inv
  hom_inv_id := by rw [sw_comp h, sg.hom_inv_id, sw_id]
  inv_hom_id := by rw [sw_comp h.inv, sg.inv_hom_id, sw_id]

/-! ### The tensor product -/

variable [MonoidalCategory C]

/-- `(A, t) ⊗ (B, s) = (A ⊗ B, t ⊗ s)`. -/
noncomputable abbrev tObj (X Y : Split C) : Split C :=
  ⟨⟨X.obj.X ⊗ Y.obj.X, X.obj.p ⊗ₘ Y.obj.p, by
    rw [tensorHom_comp_tensorHom, X.obj.idem, Y.obj.idem]⟩, trivial⟩

/-- The tensor of morphisms, `f ⊗ g`. -/
noncomputable def tHom {X₁ Y₁ X₂ Y₂ : Split C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tObj X₁ X₂ ⟶ tObj Y₁ Y₂ :=
  KCat.homMk (f.f ⊗ₘ g.f) (by
    show (X₁.obj.p ⊗ₘ X₂.obj.p) ≫ (f.f ⊗ₘ g.f) ≫ (Y₁.obj.p ⊗ₘ Y₂.obj.p) = f.f ⊗ₘ g.f
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, KCat.comp_p, KCat.comp_p,
      KCat.p_comp, KCat.p_comp])

theorem tHom_f {X₁ Y₁ X₂ Y₂ : Split C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    Karoubi.Hom.f (tHom f g) = f.f ⊗ₘ g.f := rfl

theorem tHom_eq {X₁ Y₁ X₂ Y₂ : Split C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tHom f g = sw (X := tObj X₁ X₂) (Y := tObj Y₁ Y₂) (f.f ⊗ₘ g.f) := homMk_eq_sw _ _

theorem tensor_sw {X₁ Y₁ X₂ Y₂ : Split C} (sg : X₁.obj.X ⟶ Y₁.obj.X) (tg : X₂.obj.X ⟶ Y₂.obj.X) :
    tHom (sw sg) (sw tg) = sw (X := tObj X₁ X₂) (Y := tObj Y₁ Y₂) (sg ⊗ₘ tg) := by
  refine KCat.hom_ext ?_
  rw [tHom_f, sw_f, sw_f, sw_f]
  show _ = (X₁.obj.p ⊗ₘ X₂.obj.p) ≫ (sg ⊗ₘ tg) ≫ (Y₁.obj.p ⊗ₘ Y₂.obj.p)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]

theorem wL_sw (X : Split C) {Y Z : Split C} (tg : Y.obj.X ⟶ Z.obj.X) :
    tHom (𝟙 X) (sw tg) = sw (X := tObj X Y) (Y := tObj X Z) (X.obj.X ◁ tg) := by
  rw [← sw_id X, tensor_sw, id_tensorHom]

theorem wR_sw {X Y : Split C} (sg : X.obj.X ⟶ Y.obj.X) (Z : Split C) :
    tHom (sw sg) (𝟙 Z) = sw (X := tObj X Z) (Y := tObj Y Z) (sg ▷ Z.obj.X) := by
  rw [← sw_id Z, tensor_sw, tensorHom_id]

theorem Eqv.tensor {X₁ Y₁ X₂ Y₂ : Split C} {sg : X₁.obj.X ⟶ Y₁.obj.X} {tg : X₂.obj.X ⟶ Y₂.obj.X}
    (hsg : Eqv sg) (htg : Eqv tg) : Eqv (X := tObj X₁ X₂) (Y := tObj Y₁ Y₂) (sg ⊗ₘ tg) := by
  unfold Eqv at *
  show (X₁.obj.p ⊗ₘ X₂.obj.p) ≫ (sg ⊗ₘ tg) = (sg ⊗ₘ tg) ≫ (Y₁.obj.p ⊗ₘ Y₂.obj.p)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hsg, htg]

theorem Eqv.whiskerLeft (X : Split C) {Y Z : Split C} {tg : Y.obj.X ⟶ Z.obj.X} (htg : Eqv tg) :
    Eqv (X := tObj X Y) (Y := tObj X Z) (X.obj.X ◁ tg) := by
  have := Eqv.tensor (eqv_p X) htg
  unfold Eqv at *
  show (X.obj.p ⊗ₘ Y.obj.p) ≫ (X.obj.X ◁ tg) = (X.obj.X ◁ tg) ≫ (X.obj.p ⊗ₘ Z.obj.p)
  rw [← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, htg,
    Category.comp_id, Category.id_comp]

theorem Eqv.whiskerRight {X Y : Split C} {sg : X.obj.X ⟶ Y.obj.X} (hsg : Eqv sg) (Z : Split C) :
    Eqv (X := tObj X Z) (Y := tObj Y Z) (sg ▷ Z.obj.X) := by
  unfold Eqv at *
  show (X.obj.p ⊗ₘ Z.obj.p) ≫ (sg ▷ Z.obj.X) = (sg ▷ Z.obj.X) ≫ (Y.obj.p ⊗ₘ Z.obj.p)
  rw [← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hsg,
    Category.comp_id, Category.id_comp]

theorem eqv_assoc (X Y Z : Split C) :
    Eqv (X := tObj (tObj X Y) Z) (Y := tObj X (tObj Y Z)) (α_ X.obj.X Y.obj.X Z.obj.X).hom :=
  associator_naturality _ _ _

/-! ### The unit and the unitors -/

variable [MonoidalEffectus C]

/-- The unit of `Split C`: the effect object `(I, id)`. -/
noncomputable abbrev uObj : Split C := effObj (Split C)

/-- `I ≅ 𝟙_ C` (REC 28's identification of the effect object with the tensor
unit). -/
noncomputable def uIso : effObj C ≅ 𝟙_ C := eqToIso (MonoidalEffectus.unit_eq (C := C)).symm

theorem uObj_p : (uObj (C := C)).obj.p = 𝟙 (effObj C) := rfl

theorem eqv_lam (X : Split C) :
    Eqv (X := tObj uObj X) (Y := X) (uIso.hom ▷ X.obj.X ≫ (λ_ X.obj.X).hom) := by
  unfold Eqv
  show (𝟙 (effObj C) ⊗ₘ X.obj.p) ≫ _ = _
  rw [id_tensorHom, ← Category.assoc, whisker_exchange, Category.assoc,
    leftUnitor_naturality, Category.assoc]

theorem eqv_rho (X : Split C) :
    Eqv (X := tObj X uObj) (Y := X) (X.obj.X ◁ uIso.hom ≫ (ρ_ X.obj.X).hom) := by
  unfold Eqv
  show (X.obj.p ⊗ₘ 𝟙 (effObj C)) ≫ _ = _
  rw [tensorHom_id, ← Category.assoc, ← whisker_exchange, Category.assoc,
    rightUnitor_naturality, Category.assoc]

end SplitMon

open SplitMon

variable [MonoidalCategory C] [MonoidalEffectus C]

/-- **REC 89** (short.tex:1516, Proposition), third bullet, the data: the
monoidal structure of `Split(C)` is "the same as in `C`" — `(A,t) ⊗ (B,s) =
(A ⊗ B, t ⊗ s)`, `f ⊗ g` as in `C` — with unit `id_I`, and coherence
isomorphisms modified by the idempotents, as printed: `λ_t = t ∘ λ_A ∘ (t ⊗ id_I)`
(and likewise `α`, `ρ`).  (The unitors also carry REC 28's identification
`I = 𝟙_C`.) -/
noncomputable instance splitMonoidalStruct : MonoidalCategoryStruct (Split C) where
  tensorObj := tObj
  whiskerLeft X _ _ g := tHom (𝟙 X) g
  whiskerRight f Y := tHom f (𝟙 Y)
  tensorHom := tHom
  tensorUnit := uObj
  associator X Y Z := swIso (X := tObj (tObj X Y) Z) (Y := tObj X (tObj Y Z))
    (α_ X.obj.X Y.obj.X Z.obj.X) (eqv_assoc X Y Z)
  leftUnitor X := swIso (X := tObj uObj X) (Y := X)
    (whiskerRightIso uIso X.obj.X ≪≫ λ_ X.obj.X) (eqv_lam X)
  rightUnitor X := swIso (X := tObj X uObj) (Y := X)
    (whiskerLeftIso X.obj.X uIso ≪≫ ρ_ X.obj.X) (eqv_rho X)

namespace SplitMon

theorem tensorHom_S {X₁ Y₁ X₂ Y₂ : Split C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = tHom f g := rfl

theorem whiskerLeft_S (X : Split C) {Y Z : Split C} (g : Y ⟶ Z) : X ◁ g = tHom (𝟙 X) g := rfl

theorem whiskerRight_S {X Y : Split C} (f : X ⟶ Y) (Z : Split C) : f ▷ Z = tHom f (𝟙 Z) := rfl

theorem assoc_hom_S (X Y Z : Split C) :
    (α_ X Y Z).hom = sw (X := tObj (tObj X Y) Z) (Y := tObj X (tObj Y Z))
      (α_ X.obj.X Y.obj.X Z.obj.X).hom := rfl

theorem assoc_inv_S (X Y Z : Split C) :
    (α_ X Y Z).inv = sw (X := tObj X (tObj Y Z)) (Y := tObj (tObj X Y) Z)
      (α_ X.obj.X Y.obj.X Z.obj.X).inv := rfl

theorem lam_hom_S (X : Split C) :
    (λ_ X).hom = sw (X := tObj uObj X) (Y := X) (uIso.hom ▷ X.obj.X ≫ (λ_ X.obj.X).hom) := rfl

theorem rho_hom_S (X : Split C) :
    (ρ_ X).hom = sw (X := tObj X uObj) (Y := X) (X.obj.X ◁ uIso.hom ≫ (ρ_ X.obj.X).hom) := rfl

theorem unit_S : 𝟙_ (Split C) = uObj := rfl

end SplitMon

/-- **REC 89** (short.tex:1516, Proposition), third bullet: if `C` is monoidal,
so is `Split(C)` — the monoidal category axioms.  Each axiom is the
corresponding axiom of `C`: every morphism involved is `s ∘ sg ∘ t` for a
morphism `sg` of `C` commuting with the idempotents (`SplitMon.sw`,
`SplitMon.Eqv`), and `s ∘ sg ∘ t` is functorial in such `sg` (`sw_comp`),
compatible with `⊗` (`tensor_sw`) — "using the naturality of `λ_A` it is then
straightforward to verify that this satisfies the correct equations". -/
noncomputable instance splitMonoidal : MonoidalCategory (Split C) where
  tensorHom_def f g := by
    rw [tensorHom_S, whiskerRight_S, whiskerLeft_S, ← sw_hom f, ← sw_hom g, tensor_sw, wR_sw,
      wL_sw, sw_comp ((eqv_hom f).whiskerRight _), MonoidalCategory.tensorHom_def]
  id_tensorHom_id X Y := by
    rw [tensorHom_S, ← sw_id X, ← sw_id Y, tensor_sw, MonoidalCategory.id_tensorHom_id]
    exact sw_id (tObj X Y)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    rw [tensorHom_S, tensorHom_S, tensorHom_S, ← sw_hom f₁, ← sw_hom f₂, ← sw_hom g₁,
      ← sw_hom g₂, tensor_sw, tensor_sw, sw_comp ((eqv_hom f₁).tensor (eqv_hom f₂)),
      sw_comp (eqv_hom f₁), sw_comp (eqv_hom f₂), tensor_sw, tensorHom_comp_tensorHom]
  whiskerLeft_id X Y := by
    rw [whiskerLeft_S, ← sw_id Y, wL_sw, MonoidalCategory.whiskerLeft_id]
    exact sw_id (tObj X Y)
  id_whiskerRight X Y := by
    rw [whiskerRight_S, ← sw_id X, wR_sw, MonoidalCategory.id_whiskerRight]
    exact sw_id (tObj X Y)
  associator_naturality f₁ f₂ f₃ := by
    rw [tensorHom_S, tensorHom_S, tensorHom_S, tensorHom_S, assoc_hom_S, assoc_hom_S,
      ← sw_hom f₁, ← sw_hom f₂, ← sw_hom f₃, tensor_sw, tensor_sw, tensor_sw, tensor_sw,
      sw_comp (((eqv_hom f₁).tensor (eqv_hom f₂)).tensor (eqv_hom f₃)), sw_comp (eqv_assoc _ _ _),
      associator_naturality]
  leftUnitor_naturality {X Y} f := by
    rw [whiskerLeft_S, lam_hom_S, lam_hom_S, ← sw_hom f, wL_sw,
      sw_comp ((eqv_hom f).whiskerLeft _), sw_comp (eqv_lam X)]
    congr 1
    show _ ◁ f.f ≫ uIso.hom ▷ Y.obj.X ≫ (λ_ Y.obj.X).hom = _
    rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality,
      Category.assoc]
  rightUnitor_naturality {X Y} f := by
    rw [whiskerRight_S, rho_hom_S, rho_hom_S, ← sw_hom f, wR_sw,
      sw_comp ((eqv_hom f).whiskerRight _), sw_comp (eqv_rho X)]
    congr 1
    show f.f ▷ _ ≫ Y.obj.X ◁ uIso.hom ≫ (ρ_ Y.obj.X).hom = _
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, rightUnitor_naturality,
      Category.assoc]
  pentagon W X Y Z := by
    rw [whiskerRight_S, whiskerLeft_S, assoc_hom_S, assoc_hom_S, assoc_hom_S, assoc_hom_S,
      assoc_hom_S, wR_sw, wL_sw, sw_comp (eqv_assoc W (X ⊗ Y) Z),
      sw_comp ((eqv_assoc W X Y).whiskerRight Z), sw_comp (eqv_assoc (W ⊗ X) Y Z)]
    congr 1
    exact MonoidalCategory.pentagon _ _ _ _
  triangle X Y := by
    rw [whiskerRight_S, whiskerLeft_S, assoc_hom_S, lam_hom_S, rho_hom_S, wR_sw, wL_sw,
      sw_comp (eqv_assoc _ _ _)]
    congr 1
    show (α_ X.obj.X (effObj C) Y.obj.X).hom ≫ X.obj.X ◁ (uIso.hom ▷ Y.obj.X ≫ (λ_ Y.obj.X).hom) =
      (X.obj.X ◁ uIso.hom ≫ (ρ_ X.obj.X).hom) ▷ Y.obj.X
    rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc, ← associator_naturality_middle,
      Category.assoc, MonoidalCategory.triangle, MonoidalCategory.comp_whiskerRight]

namespace SplitMon

theorem eqv_beta [BraidedCategory C] (X Y : Split C) :
    Eqv (X := tObj X Y) (Y := tObj Y X) (β_ X.obj.X Y.obj.X).hom :=
  BraidedCategory.braiding_naturality _ _

/-- The braiding of `Split C`: `β_{t,s} = (s ⊗ t) ∘ β_{A,B}`. -/
noncomputable def bIso [BraidedCategory C] (X Y : Split C) : tObj X Y ≅ tObj Y X :=
  swIso (X := tObj X Y) (Y := tObj Y X) (β_ X.obj.X Y.obj.X) (eqv_beta X Y)

theorem bIso_hom [BraidedCategory C] (X Y : Split C) :
    (bIso X Y).hom = sw (X := tObj X Y) (Y := tObj Y X) (β_ X.obj.X Y.obj.X).hom := rfl

end SplitMon

variable [SymmetricCategory C]

/-- **REC 89**, third bullet: the braiding of `Split(C)`, `β_{t,s} = (s ⊗ t) ∘ β_{A,B}`. -/
noncomputable instance splitBraided : BraidedCategory (Split C) where
  braiding := bIso
  braiding_naturality_right X {Y Z} f := by
    show tHom (𝟙 X) f ≫ (bIso X Z).hom = (bIso X Y).hom ≫ tHom f (𝟙 X)
    rw [bIso_hom, bIso_hom, ← sw_hom f, wL_sw, wR_sw, sw_comp ((eqv_hom f).whiskerLeft X),
      sw_comp (eqv_beta X Y), BraidedCategory.braiding_naturality_right]
  braiding_naturality_left {X Y} f Z := by
    show tHom f (𝟙 Z) ≫ (bIso Y Z).hom = (bIso X Z).hom ≫ tHom (𝟙 Z) f
    rw [bIso_hom, bIso_hom, ← sw_hom f, wL_sw, wR_sw, sw_comp ((eqv_hom f).whiskerRight Z),
      sw_comp (eqv_beta X Z), BraidedCategory.braiding_naturality_left]
  hexagon_forward X Y Z := by
    show (α_ X Y Z).hom ≫ (bIso X (tObj Y Z)).hom ≫ (α_ Y Z X).hom =
      tHom (bIso X Y).hom (𝟙 Z) ≫ (α_ Y X Z).hom ≫ tHom (𝟙 Y) (bIso X Z).hom
    rw [assoc_hom_S, assoc_hom_S, assoc_hom_S, bIso_hom, bIso_hom, bIso_hom, wR_sw, wL_sw,
      sw_comp (eqv_beta X (tObj Y Z)), sw_comp (eqv_assoc X Y Z), sw_comp (eqv_assoc Y X Z),
      sw_comp ((eqv_beta X Y).whiskerRight Z)]
    congr 1
    exact BraidedCategory.hexagon_forward _ _ _
  hexagon_reverse X Y Z := by
    show (α_ X Y Z).inv ≫ (bIso (tObj X Y) Z).hom ≫ (α_ Z X Y).inv =
      tHom (𝟙 X) (bIso Y Z).hom ≫ (α_ X Z Y).inv ≫ tHom (bIso X Z).hom (𝟙 Y)
    rw [assoc_inv_S, assoc_inv_S, assoc_inv_S, bIso_hom, bIso_hom, bIso_hom, wR_sw, wL_sw,
      sw_comp (eqv_beta (tObj X Y) Z), sw_comp (eqv_assoc X Y Z).inv,
      sw_comp (eqv_assoc X Z Y).inv, sw_comp ((eqv_beta Y Z).whiskerLeft X)]
    congr 1
    exact BraidedCategory.hexagon_reverse _ _ _

/-- **REC 89**, third bullet: `Split(C)` is symmetric monoidal. -/
noncomputable instance splitSymmetric : SymmetricCategory (Split C) where
  symmetry X Y := by
    show (bIso X Y).hom ≫ (bIso Y X).hom = 𝟙 (tObj X Y)
    rw [bIso_hom, bIso_hom, sw_comp (eqv_beta X Y), SymmetricCategory.symmetry]
    exact sw_id (tObj X Y)

/-- **REC 89** (short.tex:1516, Proposition), third bullet: **if `C` is a
monoidal effectus (REC 28), so is `Split(C)`**, with the symmetric monoidal
structure above: its tensor unit is its effect object `id_I`, and "the
additional equations required for a monoidal effectus" — biadditivity of `⊗`
and `1 ⊗ 1 = 1` — hold because `⊗` and truth are computed in `C` (`f ⊗ g` is
`f ⊗ g`; `1_{(A,t)} = 1_A ∘ t`). -/
theorem rec89_monoidal : MonoidalEffectus (Split C) where
  unit_eq := rfl
  ovee_tensor {A B A' B'} {f g} h k := by
    obtain ⟨h', e⟩ := MonoidalEffectus.ovee_tensor (C := C) (show Perp f.f g.f from h) k.f
    exact ⟨h', KCat.hom_ext e⟩
  zero_tensor {A B A' B'} k := KCat.hom_ext (MonoidalEffectus.zero_tensor (C := C) k.f)
  truth_tensor A B := by
    rw [eqToHom_refl, Category.id_comp]
    refine KCat.hom_ext ?_
    rw [KCat.comp_f, lam_hom_S, sw_f, tensorHom_S, tHom_f, KCat.truth_f, KCat.truth_f,
      KCat.truth_f]
    have h := MonoidalEffectus.truth_tensor (C := C) A.obj.X B.obj.X
    rw [← eqToHom_whiskerRight (MonoidalEffectus.unit_eq (C := C)).symm] at h
    show ((A.obj.p ≫ truth A.obj.X) ⊗ₘ (B.obj.p ≫ truth B.obj.X)) ≫
        (𝟙 (effObj C) ⊗ₘ 𝟙 (effObj C)) ≫ (uIso.hom ▷ effObj C ≫ (λ_ (effObj C)).hom) ≫
          𝟙 (effObj C) = (A.obj.p ⊗ₘ B.obj.p) ≫ truth (A.obj.X ⊗ B.obj.X)
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.comp_id,
      ← tensorHom_comp_tensorHom, Category.assoc, ← h]
    rfl

end SplitMonoidal

end Papers.REC
