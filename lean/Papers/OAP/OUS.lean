/-
Papers/OAP/OUS.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`, §8 *Order unit spaces*: points
**OAP 58**–**OAP 67** (OAP 64, Yosida's theorem, lives in `Yosida.lean`).

Conventions (see `Papers/README.md` and `Papers/OAP/PLAN.md`):

* An order unit space is the tree's `Theses.B.Eff.OrderUnitSpace` (a mixin
  over `AddCommGroup`, `Module ℝ`, `PartialOrder`), Archimedean is the tree's
  `OUSArchimedean`; OAP 58 proves both agree with the print's wording.
* A convex effect algebra is an effect module over `[0,1]` (the tree's
  `EffectModule I E`, 179II; the print's OAP 49).
* The unit interval `[0,1]_V` carries the tree's `orderIntervalEffectAlgebra`
  (`ousEA V`) and `orderIntervalEffectModule`; its effect-algebra order is the
  order of `V` (OAP 3, `oap3_le_iff`).
* The Gudder–Pulmannová space of a convex effect algebra `E` is the tree's
  `GP.Vec E` (179III.2), made an order unit space here with unit `GP.gunit`.
* OAP 66 needs OAP 37 (an ω-complete effect monoid is a lattice), which lives
  in `FloorCeiling.lean`; it is taken as the explicit hypothesis `oap37`.
-/
import Papers.OAP.Basic
import Papers.OAP.Yosida
import Theses.B.Eff.OrderUnit
import Theses.B.Eff.EffectAlgebras
import Mathlib.Topology.UrysohnsLemma

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u

noncomputable section

/-! ## OAP 58: order unit spaces -/

section OAP58

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- **OAP 58** (first.tex:2188, Definition): an order unit space is an
ordered vector space with a distinguished `1` such that every `v` satisfies
`-n·1 ≤ v ≤ n·1` for some `n ∈ ℕ`.  The tree's `OrderUnitSpace` asks only
for the upper bound; the lower one follows by applying it to `-v`. -/
theorem oap58_orderUnit (v : V) :
    ∃ n : ℕ, -((n : ℝ) • ouUnit V) ≤ v ∧ v ≤ (n : ℝ) • ouUnit V := by
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit v
  obtain ⟨m, hm⟩ := ou_exists_le_smul_unit (-v)
  refine ⟨max n m, ?_, ?_⟩
  · have : -v ≤ ((max n m : ℕ) : ℝ) • ouUnit V :=
      hm.trans (ou_smul_unit_mono (by exact_mod_cast le_max_right n m))
    exact neg_le.mpr this
  · exact hn.trans (ou_smul_unit_mono (by exact_mod_cast le_max_left n m))

/-- **OAP 58** (first.tex:2188, Definition): conversely, the print's data — an
ordered real vector space (translation-invariant order, positive cone closed
under non-negative scalars) with an element `1` such that every `v` lies
between `-n·1` and `n·1` — is an order unit space in the tree's sense. -/
def oap58_ofPaper (add_le : ∀ x y : V, x ≤ y → ∀ z, x + z ≤ y + z)
    (smul_nonneg : ∀ {r : ℝ} {x : V}, 0 ≤ r → 0 ≤ x → 0 ≤ r • x) (one : V)
    (h : ∀ v : V, ∃ n : ℕ, -((n : ℝ) • one) ≤ v ∧ v ≤ (n : ℝ) • one) :
    OrderUnitSpace V where
  add_le_add_left := add_le
  smul_nonneg := smul_nonneg
  unit := one
  exists_le_smul_unit v := (h v).imp fun _ h => h.2

/-- **OAP 58** (first.tex:2188, Definition): the print's Archimedean property
("`v ≤ (1/n)·1` for all `n` implies `v ≤ 0`", `n ≥ 1`) is the tree's
`OUSArchimedean` ("`v ≤ ε·1` for all `ε > 0` implies `v ≤ 0`"). -/
theorem oap58_archimedean_iff :
    OUSArchimedean V ↔
      ∀ v : V, (∀ n : ℕ, 0 < n → v ≤ (1 / (n : ℝ)) • ouUnit V) → v ≤ 0 := by
  constructor
  · intro h v hv
    refine h v fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine (hv (n + 1) n.succ_pos).trans (ou_smul_unit_mono ?_)
    push_cast
    exact hn.le
  · intro h v hv
    exact h v fun n hn => hv _ (by positivity)

end OAP58

/-! ## OAP 59: the unit interval of an order unit space -/

section OAP59

variable (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

theorem ous_posSMulMono : PosSMulMono ℝ V :=
  ⟨fun _ hc _ _ h => ou_smul_le_smul hc h⟩

theorem ous_smulPosMono : SMulPosMono ℝ V :=
  ⟨fun x hx c d hcd => by
    have h1 := ou_smul_nonneg (sub_nonneg.mpr hcd) hx
    rw [sub_smul] at h1
    exact sub_nonneg.mp h1⟩

attribute [local instance] ous_posSMulMono ous_smulPosMono

/-- **OAP 59** (first.tex:2201, Definition): the unit interval
`[0,1]_V = {v ; 0 ≤ v ≤ 1}` of an order unit space is an effect algebra with
`a ⊥ b ⟺ a + b ≤ 1`, `a ⋁ b = a + b` and `a^⊥ = 1 - a` (the tree's
`orderIntervalEffectAlgebra`). -/
abbrev ousEA : EffectAlgebra (Set.Icc (0 : V) (ouUnit V)) :=
  orderIntervalEffectAlgebra V (ouUnit V) ou_unit_nonneg

/-- **OAP 59** (first.tex:2201, Definition): "… is a *convex* effect algebra
… the convex structure being given by the obvious scalar multiplication"
(the tree's `orderIntervalEffectModule`, 179III.2). -/
abbrev ousEMod : @EffectModule I (Set.Icc (0 : V) (ouUnit V)) _ (ousEA V) :=
  orderIntervalEffectModule V (ouUnit V) ou_unit_nonneg

/-- **OAP 59** (first.tex:2201, Definition): the operations of `[0,1]_V`, as
printed. -/
theorem oap59_ops :
    (∀ a b : Set.Icc (0 : V) (ouUnit V),
      @Perp _ (ousEA V).toPCM a b ↔ (a : V) + b ≤ ouUnit V) ∧
    (∀ (a b : Set.Icc (0 : V) (ouUnit V)) (h : @Perp _ (ousEA V).toPCM a b),
      ((@ovee _ (ousEA V).toPCM a b h : Set.Icc (0 : V) (ouUnit V)) : V) = a + b) ∧
    (∀ a : Set.Icc (0 : V) (ouUnit V),
      ((@orth _ (ousEA V) a : Set.Icc (0 : V) (ouUnit V)) : V) = ouUnit V - a) ∧
    (∀ (r : I) (a : Set.Icc (0 : V) (ouUnit V)),
      ((@HSMul.hSMul I _ _ (@instHSMul _ _ (ousEMod V).toSMul) r a :
        Set.Icc (0 : V) (ouUnit V)) : V) = (r : ℝ) • (a : V)) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- **OAP 59** (first.tex:2201, Definition): `V` is **ω-complete** when
`[0,1]_V` is. -/
def OUSOmegaComplete : Prop := @OmegaComplete _ (ousEA V)

/-- **OAP 59** (first.tex:2201, Definition): `V` is **directed complete** when
`[0,1]_V` is. -/
def OUSDirectedComplete : Prop := @DirectedComplete _ (ousEA V)

end OAP59

/-! ## Suprema in `[0,1]_V`, in intervals, and in `V` -/

section LUB

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- `u` is a supremum of `S` *relative to* `A`: `u ∈ A` is an upper bound of
`S` below every upper bound of `S` that lies in `A`. -/
def IsLUBIn (A S : Set V) (u : V) : Prop :=
  u ∈ A ∧ u ∈ upperBounds S ∧ ∀ w ∈ A, w ∈ upperBounds S → u ≤ w

/-- The effect-algebra order of `[0,1]_V` is the order of `V` (OAP 3). -/
theorem ousEA_le_iff {x y : Set.Icc (0 : V) (ouUnit V)} :
    @LE.le _ (@eaPartialOrder _ (ousEA V)).toLE x y ↔ (x : V) ≤ y :=
  oap3_le_iff V _ _ x y

theorem ousEA_isLUB_iff {S : Set (Set.Icc (0 : V) (ouUnit V))} {s : Set.Icc (0 : V) (ouUnit V)} :
    @IsLUB _ (@eaPartialOrder _ (ousEA V)).toLE S s ↔
      IsLUBIn (Set.Icc 0 (ouUnit V)) (Subtype.val '' S) (s : V) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨s.2, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact ousEA_le_iff.1 (h1 hx)
    · intro w hw hub
      exact ousEA_le_iff.1 (h2 (a := ⟨w, hw⟩) fun x hx => ousEA_le_iff.2 (hub ⟨x, hx, rfl⟩))
  · rintro ⟨-, h1, h2⟩
    refine ⟨fun x hx => ousEA_le_iff.2 (h1 ⟨x, hx, rfl⟩), fun w hw => ousEA_le_iff.2 (h2 w w.2 ?_)⟩
    rintro _ ⟨x, hx, rfl⟩; exact ousEA_le_iff.1 (hw hx)

/-- `V` is ω-complete (OAP 59) iff increasing sequences in `[0,1]_V` have a
supremum relative to `[0,1]_V`. -/
theorem ousOmega_iff : OUSOmegaComplete V ↔
    ∀ f : ℕ → V, Monotone f → (∀ n, f n ∈ Set.Icc 0 (ouUnit V)) →
      ∃ u, IsLUBIn (Set.Icc 0 (ouUnit V)) (Set.range f) u := by
  let _ := ousEA V
  constructor
  · intro h f hf hmem
    let g : ℕ → Set.Icc (0 : V) (ouUnit V) := fun n => ⟨f n, hmem n⟩
    obtain ⟨s, hs⟩ := (h : @OmegaComplete _ (ousEA V)).exists_isLUB g
      (fun m n hmn => ousEA_le_iff.2 (hf hmn))
    refine ⟨s, ?_⟩
    have := ousEA_isLUB_iff.1 hs
    rwa [← Set.range_comp] at this
  · intro h
    show @OmegaComplete _ (ousEA V)
    refine ⟨fun g hg => ?_⟩
    obtain ⟨u, hu⟩ := h (fun n => (g n : V)) (fun m n hmn => ousEA_le_iff.1 (hg hmn))
      (fun n => (g n).2)
    refine ⟨⟨u, hu.1⟩, ousEA_isLUB_iff.2 ?_⟩
    rwa [← Set.range_comp]

/-- `V` is directed complete (OAP 59) iff directed subsets of `[0,1]_V` have a
supremum relative to `[0,1]_V`. -/
theorem ousDirected_iff : OUSDirectedComplete V ↔
    ∀ S : Set V, S ⊆ Set.Icc 0 (ouUnit V) → S.Nonempty → DirectedOn (· ≤ ·) S →
      ∃ u, IsLUBIn (Set.Icc 0 (ouUnit V)) S u := by
  let _ := ousEA V
  constructor
  · intro h S hS hne hd
    let T : Set (Set.Icc (0 : V) (ouUnit V)) := Subtype.val ⁻¹' S
    have hT : Subtype.val '' T = S := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hS]
    obtain ⟨x, hx⟩ := hne
    obtain ⟨s, hs⟩ := (h : @DirectedComplete _ (ousEA V)).exists_isLUB T
      ⟨⟨⟨x, hS hx⟩, hx⟩, fun a ha b hb => by
        obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
        exact ⟨⟨c, hS hc⟩, hc, ousEA_le_iff.2 hac, ousEA_le_iff.2 hbc⟩⟩
    refine ⟨s, ?_⟩
    have := ousEA_isLUB_iff.1 hs
    rwa [hT] at this
  · intro h
    show @DirectedComplete _ (ousEA V)
    refine ⟨fun T ⟨hne, hd⟩ => ?_⟩
    obtain ⟨u, hu⟩ := h (Subtype.val '' T) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (hne.image _) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hd a ha b hb
        exact ⟨c, ⟨c, hc, rfl⟩, ousEA_le_iff.1 hac, ousEA_le_iff.1 hbc⟩)
    exact ⟨⟨u, hu.1⟩, ousEA_isLUB_iff.2 hu⟩

/-- The symmetric interval `[-N·1, N·1]`. -/
abbrev symIcc (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    (N : ℝ) : Set V :=
  Set.Icc (-(N • ouUnit V)) (N • ouUnit V)

theorem symIcc_mono {N M : ℝ} (h : N ≤ M) : symIcc V N ⊆ symIcc V M := fun _ hx =>
  ⟨(neg_le_neg (ou_smul_unit_mono h)).trans hx.1, hx.2.trans (ou_smul_unit_mono h)⟩

/-- Every element lies in `[-N·1, N·1]` for all large `N`. -/
theorem exists_mem_symIcc (v : V) : ∃ N : ℕ, 0 < N ∧ ∀ M : ℝ, (N : ℝ) ≤ M → v ∈ symIcc V M := by
  obtain ⟨n, hn⟩ := oap58_orderUnit v
  refine ⟨n + 1, n.succ_pos, fun M hM => symIcc_mono ?_ hn⟩
  push_cast at hM
  linarith

/-- The affine order automorphism `v ↦ (2N)⁻¹(v + N·1)` of `V`, which maps
`[-N·1, N·1]` onto `[0,1]_V` (the print's `v ↦ nv + a`, OAP 60). -/
def affIso (N : ℝ) (hN : 0 < N) : V ≃o V where
  toFun v := (2 * N)⁻¹ • (v + N • ouUnit V)
  invFun w := (2 * N) • w - N • ouUnit V
  left_inv v := by
    simp only
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
  right_inv w := by
    simp only
    rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  map_rel_iff' := by
    intro v w
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have := ou_smul_le_smul (show (0 : ℝ) ≤ 2 * N by positivity) h
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, one_smul] at this
      exact (add_le_add_iff_right _).1 this
    · intro h
      exact ou_smul_le_smul (by positivity) (ou_add_le_add_right h _)

theorem affIso_apply (N : ℝ) (hN : 0 < N) (v : V) :
    affIso N hN v = (2 * N)⁻¹ • (v + N • ouUnit V) := rfl

theorem affIso_preimage (N : ℝ) (hN : 0 < N) :
    affIso N hN ⁻¹' Set.Icc 0 (ouUnit V) = symIcc V N := by
  have h0 : affIso N hN (-(N • ouUnit V)) = 0 := by
    rw [affIso_apply, neg_add_cancel, smul_zero]
  have h1 : affIso N hN (N • ouUnit V) = ouUnit V := by
    rw [affIso_apply, ← two_smul ℝ (N • ouUnit V), smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (by positivity), one_smul]
  ext v
  have e1 := (affIso N hN).le_iff_le (x := -(N • ouUnit V)) (y := v)
  have e2 := (affIso N hN).le_iff_le (x := v) (y := N • ouUnit V)
  rw [h0] at e1
  rw [h1] at e2
  simp only [Set.mem_preimage, Set.mem_Icc]
  rw [e1, e2]

/-- Relative suprema are transported along an order automorphism. -/
theorem IsLUBIn.of_image (g : V ≃o V) {A S : Set V} {u : V} (h : IsLUBIn A (g '' S) u) :
    IsLUBIn (g ⁻¹' A) S (g.symm u) := by
  refine ⟨by simpa using h.1, fun s hs => g.le_symm_apply.2 (h.2.1 ⟨s, hs, rfl⟩), ?_⟩
  intro w hw hub
  refine g.symm_apply_le.2 (h.2.2 _ hw ?_)
  rintro _ ⟨s, hs, rfl⟩
  exact g.le_iff_le.2 (hub hs)

/-- The print's reduction (OAP 60): a non-empty set that is bounded above and
below, and has a supremum relative to every large interval `[-N·1, N·1]`,
has a supremum in `V`.  (The relative supremum for one `N` is below every
upper bound `w`, by comparing it with the one for an `N'` with
`w ∈ [-N'·1, N'·1]`.) -/
theorem exists_isLUB_of_symIcc {S : Set V} (hne : S.Nonempty) {a b : V}
    (ha : a ∈ lowerBounds S) (hb : b ∈ upperBounds S)
    (H : ∀ N : ℕ, 0 < N → S ⊆ symIcc V N → ∃ u, IsLUBIn (symIcc V N) S u) :
    ∃ u, IsLUB S u := by
  obtain ⟨Na, hNa, hNa'⟩ := exists_mem_symIcc a
  obtain ⟨Nb, hNb, hNb'⟩ := exists_mem_symIcc b
  have hsub : ∀ M : ℕ, max Na Nb ≤ M → S ⊆ symIcc V M := fun M hM s hs =>
    ⟨(hNa' M (by exact_mod_cast (le_max_left _ _).trans hM)).1.trans (ha hs),
      (hb hs).trans (hNb' M (by exact_mod_cast (le_max_right _ _).trans hM)).2⟩
  set N := max Na Nb with hN
  have hN0 : 0 < N := lt_of_lt_of_le hNa (le_max_left _ _)
  obtain ⟨u, hu⟩ := H N hN0 (hsub N le_rfl)
  refine ⟨u, hu.2.1, fun w hw => ?_⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨Nw, hNw, hNw'⟩ := exists_mem_symIcc w
  set N' := max N Nw
  obtain ⟨u2, hu2⟩ := H N' (lt_of_lt_of_le hN0 (le_max_left _ _)) (hsub N' (le_max_left _ _))
  have hwN' : w ∈ symIcc V N' := hNw' _ (by exact_mod_cast le_max_right N Nw)
  have hu2w : u2 ≤ w := hu2.2.2 w hwN' hw
  have hNmem : (N : ℝ) • ouUnit V ∈ symIcc V N' :=
    symIcc_mono (show (N : ℝ) ≤ N' by exact_mod_cast le_max_left N Nw)
      ⟨neg_le_self (ou_smul_unit_nonneg (by positivity)), le_rfl⟩
  have hu2N : u2 ≤ (N : ℝ) • ouUnit V := hu2.2.2 _ hNmem fun s hs =>
    (hb hs).trans (hNb' N (by exact_mod_cast le_max_right Na Nb)).2
  have hu2S : u2 ∈ symIcc V N :=
    ⟨(hsub N le_rfl hs0).1.trans (hu2.2.1 hs0), hu2N⟩
  exact (hu.2.2 u2 hu2S hu2.2.1).trans hu2w

end LUB

/-! ## OAP 60, OAP 61: bounded completeness and the Archimedean property -/

section OAP60

variable (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]

/-- **OAP 60** (`lem:completenessousemod`, first.tex:2213, Lemma): `V` is
**bounded directed complete** when every non-empty directed subset of `V`
with an upper bound has a supremum. -/
def OUSBoundedDirectedComplete : Prop :=
  ∀ S : Set V, S.Nonempty → DirectedOn (· ≤ ·) S → BddAbove S → ∃ u, IsLUB S u

/-- **OAP 60** (`lem:completenessousemod`, first.tex:2213, Lemma): `V` is
**bounded ω-complete** when every increasing sequence in `V` with an upper
bound has a supremum. -/
def OUSBoundedOmegaComplete : Prop :=
  ∀ f : ℕ → V, Monotone f → BddAbove (Set.range f) → ∃ u, IsLUB (Set.range f) u

variable {V}

/-- **OAP 60** (`lem:completenessousemod`, first.tex:2213, Lemma): an order
unit space is directed complete iff it is bounded directed complete.  As
printed: for a bounded directed `S` pick `a ∈ S`, pass to
`S' = {v ∈ S ; a ≤ v}`, and move `S'` into `[0,1]_V` by an affine order
isomorphism (the print's `{(1/n)(s - a)}` lies in `[0,2]_V`, not `[0,1]_V`,
so we use `v ↦ (2N)⁻¹(v + N·1)`); `exists_isLUB_of_symIcc` then shows the
supremum found in the interval is one in `V`. -/
theorem oap60_directed : OUSDirectedComplete V ↔ OUSBoundedDirectedComplete V := by
  constructor
  · intro h S hne hd ⟨b, hb⟩
    obtain ⟨a, haS⟩ := hne
    set S' := {v ∈ S | a ≤ v} with hS'
    have hS'S : S' ⊆ S := fun v hv => hv.1
    have hd' : DirectedOn (· ≤ ·) S' := by
      rintro x ⟨hx, hax⟩ y ⟨hy, -⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hd x hx y hy
      exact ⟨z, ⟨hz, hax.trans hxz⟩, hxz, hyz⟩
    have hcof : ∀ s ∈ S, ∃ z ∈ S', s ≤ z := fun s hs => by
      obtain ⟨z, hz, hsz, haz⟩ := hd s hs a haS
      exact ⟨z, ⟨hz, haz⟩, hsz⟩
    obtain ⟨u, hu⟩ : ∃ u, IsLUB S' u := by
      refine exists_isLUB_of_symIcc ⟨a, haS, le_rfl⟩ (fun v hv => hv.2) (fun v hv => hb hv.1) ?_
      intro N hN hsub
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      let g := affIso (V := V) N hN'
      obtain ⟨u', hu'⟩ := ousDirected_iff.1 h (g '' S')
        (by rintro _ ⟨v, hv, rfl⟩; rw [← Set.mem_preimage, affIso_preimage]; exact hsub hv)
        ⟨g a, a, ⟨haS, le_rfl⟩, rfl⟩
        (by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          obtain ⟨z, hz, hxz, hyz⟩ := hd' x hx y hy
          exact ⟨g z, ⟨z, hz, rfl⟩, g.le_iff_le.2 hxz, g.le_iff_le.2 hyz⟩)
      have := hu'.of_image g
      rw [affIso_preimage] at this
      exact ⟨_, this⟩
    refine ⟨u, fun s hs => ?_, fun w hw => hu.2 fun v hv => hw (hS'S hv)⟩
    obtain ⟨z, hz, hsz⟩ := hcof s hs
    exact hsz.trans (hu.1 hz)
  · intro h
    refine ousDirected_iff.2 fun S hS hne hd => ?_
    obtain ⟨u, hu⟩ := h S hne hd ⟨ouUnit V, fun s hs => (hS hs).2⟩
    obtain ⟨s0, hs0⟩ := hne
    exact ⟨u, ⟨(hS hs0).1.trans (hu.1 hs0), hu.2 fun s hs => (hS hs).2⟩, hu.1,
      fun w _ hw => hu.2 hw⟩

/-- **OAP 60** (`lem:completenessousemod`, first.tex:2213, Lemma), "similarly":
an order unit space is ω-complete iff it is bounded ω-complete. -/
theorem oap60_omega : OUSOmegaComplete V ↔ OUSBoundedOmegaComplete V := by
  constructor
  · intro h f hf ⟨b, hb⟩
    refine exists_isLUB_of_symIcc (Set.range_nonempty f) (a := f 0)
      (by rintro _ ⟨n, rfl⟩; exact hf (Nat.zero_le n)) hb ?_
    intro N hN hsub
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    let g := affIso (V := V) N hN'
    obtain ⟨u', hu'⟩ := ousOmega_iff.1 h (g ∘ f) (g.monotone.comp hf)
      (fun n => by
        show g (f n) ∈ _
        rw [← Set.mem_preimage, affIso_preimage]; exact hsub ⟨n, rfl⟩)
    rw [Set.range_comp] at hu'
    have := hu'.of_image g
    rw [affIso_preimage] at this
    exact ⟨_, this⟩
  · intro h
    refine ousOmega_iff.2 fun f hf hmem => ?_
    obtain ⟨u, hu⟩ := h f hf ⟨ouUnit V, by rintro _ ⟨n, rfl⟩; exact (hmem n).2⟩
    exact ⟨u, ⟨(hmem 0).1.trans (hu.1 ⟨0, rfl⟩), hu.2 (by rintro _ ⟨n, rfl⟩; exact (hmem n).2)⟩,
      hu.1, fun w _ hw => hu.2 hw⟩

/-- **OAP 61** (`boundeddircomplisarchous`, first.tex:2235, Lemma): a bounded
ω-complete order unit space is Archimedean.  As printed: the infimum of
`(1/n)·1` exists (the supremum of `-(1/n)·1`), and is `0` — the print's
"`⋀ₙ (1/n)·1 = (inf 1/n)·1`" is justified by noting that twice the infimum
is again a lower bound. -/
theorem oap61 (h : OUSBoundedOmegaComplete V) : OUSArchimedean V := by
  intro v hv
  let f : ℕ → V := fun n => -((1 / ((n : ℝ) + 1)) • ouUnit V)
  have hf : Monotone f := monotone_nat_of_le_succ fun n => neg_le_neg
    (ou_smul_unit_mono (one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)))
  obtain ⟨s, hs⟩ := h f hf ⟨0, by
    rintro _ ⟨n, rfl⟩; exact neg_nonpos.2 (ou_smul_unit_nonneg (by positivity))⟩
  -- `2s` is an upper bound, since `f n = 2 f (2n+1)`
  have h2 : (2 : ℝ) • s ∈ upperBounds (Set.range f) := by
    rintro _ ⟨n, rfl⟩
    have e : f n = (2 : ℝ) • f (2 * n + 1) := by
      simp only [f, smul_neg, smul_smul]
      congr 2
      push_cast
      field_simp
      ring
    rw [e]
    exact ou_smul_le_smul (by norm_num) (hs.1 ⟨_, rfl⟩)
  have hs0 : 0 ≤ s := by
    have := hs.2 h2
    rw [two_smul] at this
    exact (le_add_iff_nonneg_right s).1 this
  have hv' : -v ∈ upperBounds (Set.range f) := by
    rintro _ ⟨n, rfl⟩
    exact neg_le_neg (hv _ (by positivity))
  have := hs.2 hv'
  exact (le_neg.1 this).trans (neg_nonpos.2 hs0)

/-- The print's route to norm-completeness in OAP 66 cites Wright
[Lemma 1.2]: a bounded ω-complete order unit space is complete in its
order-unit norm.  Ours (Wright's argument): pass to a subsequence `uₖ` with
`|u_j - u_k| ≤ 2⁻ᵏ` for `j ≥ k`; `uₖ - 2·2⁻ᵏ·1` increases and is bounded,
and its supremum is the limit. -/
theorem wright_normComplete (h : OUSBoundedOmegaComplete V) : OUSNormComplete V := by
  intro s hs
  choose Nf hNf using fun k : ℕ => hs ((1 / 2 : ℝ) ^ k) (by positivity)
  let n : ℕ → ℕ := fun k => k + (Finset.range (k + 1)).sup Nf
  have hnmono : Monotone n := fun i j hij =>
    add_le_add hij (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hij)))
  have hnk : ∀ k, Nf k ≤ n k := fun k =>
    le_add_left (Finset.le_sup (f := Nf) (Finset.self_mem_range_succ k))
  have hkn : ∀ k, k ≤ n k := fun k => Nat.le_add_right _ _
  let u : ℕ → V := fun k => s (n k)
  have hu : ∀ k j, k ≤ j → u j - u k ≤ ((1 / 2 : ℝ) ^ k) • ouUnit V ∧
      u k - u j ≤ ((1 / 2 : ℝ) ^ k) • ouUnit V := fun k j hkj =>
    ⟨hNf k _ ((hnk k).trans (hnmono hkj)) _ (hnk k),
      hNf k _ (hnk k) _ ((hnk k).trans (hnmono hkj))⟩
  let w : ℕ → V := fun k => u k - (2 * (1 / 2 : ℝ) ^ k) • ouUnit V
  have hw : Monotone w := monotone_nat_of_le_succ fun k => by
    have h1 := (hu k (k + 1) (Nat.le_succ k)).2
    have e : u (k + 1) - (2 * (1 / 2 : ℝ) ^ (k + 1)) • ouUnit V
        - (u k - (2 * (1 / 2 : ℝ) ^ k) • ouUnit V)
        = ((1 / 2 : ℝ) ^ k) • ouUnit V - (u k - u (k + 1)) := by
      rw [pow_succ]; module
    exact sub_nonneg.1 (e ▸ sub_nonneg.2 h1)
  have hwu : ∀ k, w k ≤ u k := fun k =>
    sub_le_self _ (ou_smul_unit_nonneg (by positivity))
  obtain ⟨v, hv⟩ := h w hw ⟨u 0 + ouUnit V, by
    rintro _ ⟨k, rfl⟩
    have := (hu 0 k (Nat.zero_le k)).1
    rw [pow_zero, one_smul] at this
    exact (hwu k).trans (sub_le_iff_le_add'.1 this)⟩
  have hlow : ∀ k, u k - v ≤ (2 * (1 / 2 : ℝ) ^ k) • ouUnit V := fun k =>
    sub_le_comm.1 (hv.1 ⟨k, rfl⟩)
  have hup : ∀ k, v - u k ≤ (2 * (1 / 2 : ℝ) ^ k) • ouUnit V := by
    intro k
    refine sub_le_iff_le_add'.2 (hv.2 ?_)
    rintro _ ⟨j, rfl⟩
    rcases le_total j k with hjk | hkj
    · exact (hw hjk).trans ((hwu k).trans
        (le_add_of_nonneg_right (ou_smul_unit_nonneg (by positivity))))
    · refine (hwu j).trans ((sub_le_iff_le_add'.1 (hu k j hkj).1).trans ?_)
      exact add_le_add le_rfl (ou_smul_unit_mono (by
        have : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
        linarith))
  refine ⟨v, fun ε hε => ?_⟩
  obtain ⟨N0, hN0⟩ := hs (ε / 2) (by positivity)
  obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set k := max k0 N0
  have hk : 2 * (1 / 2 : ℝ) ^ k ≤ ε / 2 := by
    have : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ k0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
    linarith
  have hNk : N0 ≤ n k := (le_max_right k0 N0).trans (hkn k)
  refine ⟨N0, fun m hm => ⟨?_, ?_⟩⟩
  · calc s m - v = (s m - u k) + (u k - v) := by abel
      _ ≤ (ε / 2) • ouUnit V + (2 * (1 / 2 : ℝ) ^ k) • ouUnit V :=
        add_le_add (hN0 m hm (n k) hNk) (hlow k)
      _ = (ε / 2 + 2 * (1 / 2 : ℝ) ^ k) • ouUnit V := (add_smul _ _ _).symm
      _ ≤ ε • ouUnit V := ou_smul_unit_mono (by linarith)
  · calc v - s m = (v - u k) + (u k - s m) := by abel
      _ ≤ (2 * (1 / 2 : ℝ) ^ k) • ouUnit V + (ε / 2) • ouUnit V :=
        add_le_add (hup k) (hN0 (n k) hNk m hm)
      _ = (2 * (1 / 2 : ℝ) ^ k + ε / 2) • ouUnit V := (add_smul _ _ _).symm
      _ ≤ ε • ouUnit V := ou_smul_unit_mono (by linarith)

end OAP60

/-! ## OAP 62: the Gudder–Pulmannová representation -/

section OAP62

variable {E : Type u} [EffectAlgebra E] [EffectModule I E]

/-- The Gudder–Pulmannová space `GP.Vec E` of a convex effect algebra (tree,
179III.2) is an order unit space with unit `GP.gunit`. -/
instance gpOrderUnitSpace : OrderUnitSpace (GP.Vec E) where
  add_le_add_left _ _ h z := add_le_add_left h z
  smul_nonneg hr hx := smul_nonneg hr hx
  unit := GP.gunit
  exists_le_smul_unit v := by
    obtain ⟨n, hn⟩ := GP.isOrderUnit_gunit v
    exact ⟨n, by rwa [Nat.cast_smul_eq_nsmul]⟩

theorem gp_ouUnit : ouUnit (GP.Vec E) = GP.gunit := rfl

/-- The scalar `1/2 ∈ [0,1]`. -/
def ihalf : I := ⟨1 / 2, by norm_num, by norm_num⟩

theorem ihalf_perp : Perp ihalf ihalf := by
  rw [GP.I_perp_iff]; show (1 / 2 : ℝ) + 1 / 2 ≤ 1; norm_num

theorem ihalf_ovee : ovee ihalf ihalf ihalf_perp = (1 : I) :=
  Subtype.ext (by rw [GP.I_coe_ovee]; show (1 / 2 : ℝ) + 1 / 2 = 1; norm_num)

/-- `x = ½x ⋁ ½x` in a convex effect algebra. -/
theorem half_oplus_half (x : E) :
    Perp (ihalf • x) (ihalf • x) ∧ ihalf • x ⋎ ihalf • x = x := by
  obtain ⟨h, e⟩ := EffectModule.perp_smul (E := E) ihalf_perp x
  refine ⟨h, ?_⟩
  rw [oplus_eq h, e, ihalf_ovee, EffectModule.one_smul]

/-- Halving is cancellable: `½a ⋁ ½c = ½b` implies `a ⊥ c` and `a ⋁ c = b`. -/
theorem half_cancel {a b c : E} (h : Perp (ihalf • a) (ihalf • c))
    (e : ihalf • a ⋎ ihalf • c = ihalf • b) : Perp a c ∧ a ⋎ c = b := by
  obtain ⟨hb, eb⟩ := half_oplus_half b
  obtain ⟨ha, ea⟩ := half_oplus_half a
  obtain ⟨hc, ec⟩ := half_oplus_half c
  rw [← e] at hb eb
  obtain ⟨-, -, hac, e'⟩ := oplus_oplus_comm h h hb
  rw [ea, ec] at hac e'
  exact ⟨hac, e'.symm.trans eb⟩

theorem gmap_half_add (a c : E) :
    GP.gmap (ihalf • a ⋎ ihalf • c) = (1 / 2 : ℝ) • (GP.gmap a + GP.gmap c) := by
  have hp : Perp (ihalf • a) (ihalf • c) := GP.smul_perp_smul' ihalf_perp a c
  rw [oplus_eq hp, GP.gmap_ovee, GP.gmap_smul, GP.gmap_smul, smul_add]
  rfl

/-- The Gudder–Pulmannová embedding reflects (and preserves) the order. -/
theorem gmap_le_gmap_iff {a b : E} : GP.gmap a ≤ GP.gmap b ↔ a ≤ b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := GP.gmap_surjective_Icc (x := GP.gmap b - GP.gmap a)
      ⟨sub_nonneg.2 h, (sub_le_self _ (GP.gmap_nonneg a)).trans (GP.gmap_le_gunit b)⟩
    have hp : Perp (ihalf • a) (ihalf • c) := GP.smul_perp_smul' ihalf_perp a c
    have e : ihalf • a ⋎ ihalf • c = ihalf • b := by
      apply GP.gmap_injective
      rw [gmap_half_add, GP.gmap_smul, hc, add_sub_cancel]
      rfl
    obtain ⟨hac, e'⟩ := half_cancel hp e
    exact le_def.2 ⟨c, hac, e'⟩
  · intro h
    obtain ⟨c, hac, rfl⟩ := le_def.1 h
    rw [oplus_eq hac, GP.gmap_ovee]
    exact le_add_of_nonneg_right (GP.gmap_nonneg c)

theorem gmap_add_orth (a : E) : GP.gmap a + GP.gmap (orth a) = GP.gunit := by
  rw [← GP.gmap_ovee (EffectAlgebra.perp_orth a), EffectAlgebra.ovee_orth]; rfl

/-- The Gudder–Pulmannová embedding reflects orthogonality. -/
theorem gmap_perp_iff {a b : E} : Perp a b ↔ GP.gmap a + GP.gmap b ≤ GP.gunit := by
  constructor
  · intro h
    rw [← GP.gmap_ovee h]; exact GP.gmap_le_gunit _
  · intro h
    have hb : GP.gmap b ≤ GP.gmap (orth a) := by
      rw [← gmap_add_orth a] at h
      exact (add_le_add_iff_left _).1 h
    exact perp_symm.1 (perp_iff_le_orth.2 (gmap_le_gmap_iff.1 hb))

/-- The Gudder–Pulmannová map as an equivalence `E ≃ [0,1]_{GP.Vec E}`. -/
def gpEquiv (E : Type u) [EffectAlgebra E] [EffectModule I E] :
    E ≃ Set.Icc (0 : GP.Vec E) (ouUnit (GP.Vec E)) :=
  Equiv.ofBijective (fun a => ⟨GP.gmap a, GP.gmap_nonneg a, GP.gmap_le_gunit a⟩)
    ⟨fun _ _ h => GP.gmap_injective (congrArg Subtype.val h),
      fun y => (GP.gmap_surjective_Icc y.2).imp fun _ h => Subtype.ext h⟩

@[simp] theorem gpEquiv_apply (a : E) : (gpEquiv E a : GP.Vec E) = GP.gmap a := rfl

/-- **OAP 62** (`prop:convextotalisation`, first.tex:2249, Theorem;
Gudder–Pulmannová): every convex effect algebra `M` is isomorphic, as a convex
effect algebra, to the unit interval `[0,1]_V` of an order unit space `V`.
The isomorphism is a bijection that preserves and reflects `⊥`, preserves
`⋁`, `1` and the scalar multiplication, and is an order isomorphism.  The
print cites [Gudder–Pulmannová]; the tree proves the representation
(179III.2, `effectModule_unitInterval_representation`, cone-and-differences
construction `GP.Vec`), and reflection of `⊥` and of the order is added here
(`gmap_perp_iff`, `gmap_le_gmap_iff`, by halving). -/
theorem oap62 (M : Type u) [EffectAlgebra M] [EffectModule I M] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : PartialOrder V)
      (_ : OrderUnitSpace V) (e : M ≃ Set.Icc (0 : V) (ouUnit V)),
      (∀ a b : M, Perp a b ↔ (e a : V) + e b ≤ ouUnit V) ∧
      (∀ (a b : M) (h : Perp a b), (e (ovee a b h) : V) = e a + e b) ∧
      (e 1 : V) = ouUnit V ∧
      (∀ (r : I) (a : M), (e (r • a) : V) = (r : ℝ) • (e a : V)) ∧
      (∀ a b : M, a ≤ b ↔ (e a : V) ≤ e b) :=
  ⟨GP.Vec M, inferInstance, inferInstance, inferInstance, inferInstance, gpEquiv M,
    fun _ _ => gmap_perp_iff, fun _ _ h => GP.gmap_ovee h, rfl,
    fun r a => GP.gmap_smul r a, fun _ _ => gmap_le_gmap_iff.symm⟩

end OAP62

/-! ## Completeness of the Gudder–Pulmannová space; OAP 63 -/

section GPComplete

variable {E : Type u} [EffectAlgebra E] [EffectModule I E]

/-- Suprema in `E` are suprema in `[0,1]_{GP.Vec E}` and conversely. -/
theorem gmap_isLUBIn_iff {S : Set E} {s : E} :
    IsLUB S s ↔ IsLUBIn (Set.Icc 0 (ouUnit (GP.Vec E))) (GP.gmap '' S) (GP.gmap s) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨GP.gmap_nonneg s, GP.gmap_le_gunit s⟩, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact gmap_le_gmap_iff.2 (h1 hx)
    · intro w hw hub
      obtain ⟨t, rfl⟩ := GP.gmap_surjective_Icc hw
      exact gmap_le_gmap_iff.2 (h2 fun x hx => gmap_le_gmap_iff.1 (hub ⟨x, hx, rfl⟩))
  · rintro ⟨-, h1, h2⟩
    refine ⟨fun x hx => gmap_le_gmap_iff.1 (h1 ⟨x, hx, rfl⟩), fun t ht => ?_⟩
    refine gmap_le_gmap_iff.1 (h2 _ ⟨GP.gmap_nonneg t, GP.gmap_le_gunit t⟩ ?_)
    rintro _ ⟨x, hx, rfl⟩; exact gmap_le_gmap_iff.2 (ht hx)

/-- If `E` is ω-complete, so is `GP.Vec E` (OAP 59). -/
theorem gp_omegaComplete [OmegaComplete E] : OUSOmegaComplete (GP.Vec E) := by
  refine ousOmega_iff.2 fun f hf hmem => ?_
  choose g hg using fun n => GP.gmap_surjective_Icc (hmem n)
  have hgm : Monotone g := fun m n hmn => gmap_le_gmap_iff.1 (by rw [hg, hg]; exact hf hmn)
  obtain ⟨s, hs⟩ := OmegaComplete.exists_isLUB g hgm
  refine ⟨GP.gmap s, ?_⟩
  have := gmap_isLUBIn_iff.1 hs
  rwa [← Set.range_comp, show GP.gmap ∘ g = f from funext hg] at this

/-- If `E` is directed complete, so is `GP.Vec E` (OAP 59). -/
theorem gp_directedComplete [DirectedComplete E] : OUSDirectedComplete (GP.Vec E) := by
  refine ousDirected_iff.2 fun S hS hne hd => ?_
  set T : Set E := GP.gmap ⁻¹' S
  have hT : GP.gmap '' T = S := by
    ext x; constructor
    · rintro ⟨t, ht, rfl⟩; exact ht
    · intro hx
      obtain ⟨t, rfl⟩ := GP.gmap_surjective_Icc (hS hx)
      exact ⟨t, hx, rfl⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t0, rfl⟩ := GP.gmap_surjective_Icc (hS hx)
  obtain ⟨s, hs⟩ := DirectedComplete.exists_isLUB T ⟨⟨t0, hx⟩, fun a ha b hb => by
    obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
    obtain ⟨c', rfl⟩ := GP.gmap_surjective_Icc (hS hc)
    exact ⟨c', hc, gmap_le_gmap_iff.1 hac, gmap_le_gmap_iff.1 hbc⟩⟩
  refine ⟨GP.gmap s, ?_⟩
  have := gmap_isLUBIn_iff.1 hs
  rwa [hT] at this

/-- For ω-complete `E` the space `GP.Vec E` is Archimedean (OAP 60, 61). -/
theorem gp_archimedean [OmegaComplete E] : OUSArchimedean (GP.Vec E) :=
  oap61 (oap60_omega.1 gp_omegaComplete)

/-- The core of OAP 63: an additive map `F : E → V` with `0 ≤ F b ≤ b` is
homogeneous for `[0,1]`-scalars when `V` is Archimedean.  Rational scalars
`k/n` by additivity; for general `λ`, with `q = ⌊nλ⌋/n` and `r = λ - q`,
`F(λb) - λF(b) = F(rb) - rF(b)` lies between `-r·1` and `r·1` — the print's
norm estimate `‖λ(a·b) - a·(λb)‖ ≤ 2(λ - qᵢ)` in order form. -/
theorem additive_smul (hA : OUSArchimedean (GP.Vec E)) (F : E → GP.Vec E)
    (hadd : ∀ {b c : E} (_ : Perp b c), F (b ⋎ c) = F b + F c)
    (h0 : ∀ b, 0 ≤ F b) (hle : ∀ b, F b ≤ GP.gmap b) (l : I) (b : E) :
    F (l • b) = (l : ℝ) • F b := by
  have hrat : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k ≤ n →
      F (GP.Iv ((k : ℝ) / n) • b) = ((k : ℝ) / n) • F b := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have step : ∀ k : ℕ, k ≤ n →
        F (GP.Iv ((k : ℝ) / n) • b) = (k : ℝ) • F (GP.Iv (1 / (n : ℝ)) • b) := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [Nat.cast_zero, zero_div, GP.Iv_zero, GP.zero_smul', zero_smul]
        exact le_antisymm ((hle 0).trans GP.gmap_zero.le) (h0 0)
      | succ k ih =>
        intro hk
        have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
        have hsum : (k : ℝ) / n + 1 / n ≤ 1 := by
          rw [← add_div, div_le_one hn']; exact hk'
        have hp := GP.Iv_perp (by positivity) (by positivity) hsum
        obtain ⟨hb', eb⟩ := EffectModule.perp_smul hp b
        rw [GP.Iv_ovee (by positivity) (by positivity) hsum hp] at eb
        rw [show ((k + 1 : ℕ) : ℝ) / n = (k : ℝ) / n + 1 / n by push_cast; ring, ← eb,
          ← oplus_eq hb', hadd hb', ih (by omega)]
        push_cast
        rw [add_smul, one_smul]
    intro k hk
    have hn1 := step n le_rfl
    rw [div_self hn'.ne', GP.Iv_one, EffectModule.one_smul] at hn1
    rw [step k hk, hn1, smul_smul]
    congr 1
    field_simp
  have hFu : ∀ c, F c ≤ GP.gunit := fun c => (hle c).trans (GP.gmap_le_gunit c)
  have key : ∀ ε : ℝ, 0 < ε → F (l • b) - (l : ℝ) • F b ≤ ε • GP.gunit ∧
      -(F (l • b) - (l : ℝ) • F b) ≤ ε • GP.gunit := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hl0 : (0 : ℝ) ≤ l := l.2.1
    have hl1 : (l : ℝ) ≤ 1 := l.2.2
    have hlN : (0 : ℝ) ≤ (l : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
    have hk1 : ((⌊(l : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ (l : ℝ) * ((n + 1 : ℕ) : ℝ) :=
      Nat.floor_le hlN
    have hk2 : (l : ℝ) * ((n + 1 : ℕ) : ℝ) < ((⌊(l : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    set k := ⌊(l : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊
    have hkN : k ≤ n + 1 := by
      have : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := hk1.trans (by nlinarith)
      exact_mod_cast this
    set q : ℝ := (k : ℝ) / ((n + 1 : ℕ) : ℝ)
    have hq0 : 0 ≤ q := by positivity
    have hql : q ≤ l := by rw [div_le_iff₀ hN]; exact hk1
    have hlq : (l : ℝ) - q < 1 / ((n + 1 : ℕ) : ℝ) := by
      have : (l : ℝ) < q + 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [show q + 1 / ((n + 1 : ℕ) : ℝ) = ((k : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) by
          simp only [q]; ring, lt_div_iff₀ hN]
        exact hk2
      linarith
    set r : ℝ := (l : ℝ) - q
    have hr0 : 0 ≤ r := by simp only [r]; linarith
    have hrε : r ≤ ε := by
      have : 1 / ((n + 1 : ℕ) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; ring
      linarith
    have hqr : q + r ≤ 1 := by simp only [r]; linarith
    have hp := GP.Iv_perp hq0 hr0 hqr
    obtain ⟨hb', eb⟩ := EffectModule.perp_smul hp b
    rw [GP.Iv_ovee hq0 hr0 hqr hp, show q + r = (l : ℝ) by simp only [r]; ring,
      GP.Iv_self] at eb
    have eF : F (l • b) = q • F b + F (GP.Iv r • b) := by
      rw [← eb, ← oplus_eq hb', hadd hb', hrat _ (Nat.succ_pos n) k hkN]
    have ex : F (l • b) - (l : ℝ) • F b = F (GP.Iv r • b) - r • F b := by
      rw [eF, show (l : ℝ) = q + r by simp only [r]; ring, add_smul]; abel
    have hFr : F (GP.Iv r • b) ≤ r • GP.gunit := by
      refine (hle _).trans ?_
      rw [GP.gmap_smul, GP.Iv_coe hr0 (by linarith)]
      exact ou_smul_le_smul hr0 (GP.gmap_le_gunit b)
    have hrF : r • F b ≤ r • GP.gunit := ou_smul_le_smul hr0 (hFu b)
    have hεu : r • GP.gunit ≤ ε • (GP.gunit : GP.Vec E) := ou_smul_unit_mono (X := GP.Vec E) hrε
    rw [ex]
    constructor
    · exact (sub_le_self _ (ou_smul_nonneg hr0 (h0 b))).trans (hFr.trans hεu)
    · rw [neg_sub]
      exact (sub_le_self _ (h0 _)).trans (hrF.trans hεu)
  have h1 := hA _ fun ε hε => (key ε hε).1
  have h2 := hA _ fun ε hε => (key ε hε).2
  exact sub_eq_zero.1 (le_antisymm h1 (neg_nonpos.1 h2))

end GPComplete

section OAP63

variable {M : Type u} [EffectMonoid M] [EffectModule I M]

/-- **OAP 63** (`prop:multiplicationisbilinear`, first.tex:2334, Proposition):
in an ω-complete convex effect monoid the multiplication is "bilinear":
`λ(a·b) = (λa)·b = a·(λb)` for `a, b ∈ M` and `λ ∈ [0,1]`.  As printed:
first for rational `λ` by additivity, then for real `λ` by approximating
from below with rationals `q` and the estimate `±(λ(a·b) - a·(λb)) ≤ 2(λ-q)·1`
in the Gudder–Pulmannová space `V` (OAP 62), which is Archimedean by OAP 60
and OAP 61 (`additive_smul`). -/
theorem oap63 [OmegaComplete M] (l : I) (a b : M) :
    l • (a * b) = (l • a) * b ∧ l • (a * b) = a * (l • b) := by
  have hA : OUSArchimedean (GP.Vec M) := gp_archimedean
  constructor
  · have := additive_smul hA (fun x => GP.gmap (x * b))
      (fun h => by rw [(oplus_mul b h).2, oplus_eq (oplus_mul b h).1, GP.gmap_ovee])
      (fun x => GP.gmap_nonneg _) (fun x => gmap_le_gmap_iff.2 (emul_le_left x b)) l a
    apply GP.gmap_injective
    rw [GP.gmap_smul]
    exact this.symm
  · have := additive_smul hA (fun x => GP.gmap (a * x))
      (fun h => by rw [(mul_oplus a h).2, oplus_eq (mul_oplus a h).1, GP.gmap_ovee])
      (fun x => GP.gmap_nonneg _) (fun x => gmap_le_gmap_iff.2 (emul_le_right a x)) l b
    apply GP.gmap_injective
    rw [GP.gmap_smul]
    exact this.symm

end OAP63

/-! ## OAP 66: convex ω-complete effect monoids are `[0,1]_{C(X)}` -/

section Lattice

variable {V : Type u} [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V]

/-- An ordered abelian group in which every pair has a supremum is a lattice
(`x ⊓ y = -((-x) ⊔ (-y))`), *with its given order*: the lattice's
`≤` is definitionally the given one, which is what lets Yosida's theorem
(stated over `[Lattice V] [OrderUnitSpace V]`) apply to `GP.Vec M`. -/
abbrev vecLattice (h : ∀ x y : V, ∃ u, IsLUB ({x, y} : Set V) u) : Lattice V :=
  { (inferInstance : PartialOrder V) with
    sup := fun x y => Classical.choose (h x y)
    le_sup_left := fun x y => (Classical.choose_spec (h x y)).1 (Set.mem_insert _ _)
    le_sup_right := fun x y => (Classical.choose_spec (h x y)).1 (Set.mem_insert_of_mem _ rfl)
    sup_le := fun x y z hx hy => (Classical.choose_spec (h x y)).2 (by
      rintro w (rfl | rfl) <;> assumption)
    inf := fun x y => -Classical.choose (h (-x) (-y))
    inf_le_left := fun x y =>
      neg_le.mpr ((Classical.choose_spec (h (-x) (-y))).1 (Set.mem_insert _ _))
    inf_le_right := fun x y =>
      neg_le.mpr ((Classical.choose_spec (h (-x) (-y))).1 (Set.mem_insert_of_mem _ rfl))
    le_inf := fun x y z hy hz => le_neg.mpr ((Classical.choose_spec (h (-y) (-z))).2 (by
      rintro w (rfl | rfl)
      · exact neg_le_neg hy
      · exact neg_le_neg hz)) }

end Lattice

section GPSup

variable {E : Type u} [EffectAlgebra E] [EffectModule I E]

/-- The print's "`V` is a lattice as well, as any supremum reduces to one in
the interval `[0,1]_V`" (proof of OAP 66): binary suprema in `E` give binary
suprema in `GP.Vec E`. -/
theorem gp_sup (h : ∀ a b : E, ∃ c, IsLUB ({a, b} : Set E) c) (x y : GP.Vec E) :
    ∃ u, IsLUB ({x, y} : Set (GP.Vec E)) u := by
  obtain ⟨Nx, -, hNx'⟩ := exists_mem_symIcc x
  obtain ⟨Ny, -, hNy'⟩ := exists_mem_symIcc y
  have hxN := hNx' ((max Nx Ny : ℕ) : ℝ) (by exact_mod_cast le_max_left _ _)
  have hyN := hNy' ((max Nx Ny : ℕ) : ℝ) (by exact_mod_cast le_max_right _ _)
  refine exists_isLUB_of_symIcc (Set.insert_nonempty _ _)
    (a := -(((max Nx Ny : ℕ) : ℝ) • ouUnit _)) (b := ((max Nx Ny : ℕ) : ℝ) • ouUnit _)
    ?_ ?_ ?_
  · rintro z (rfl | rfl)
    exacts [hxN.1, hyN.1]
  · rintro z (rfl | rfl)
    exacts [hxN.2, hyN.2]
  · intro K hK hsub
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    let g := affIso (V := GP.Vec E) K hK'
    have hmem : ∀ z ∈ ({x, y} : Set (GP.Vec E)), g z ∈ Set.Icc 0 (ouUnit (GP.Vec E)) :=
      fun z hz => by rw [← Set.mem_preimage, affIso_preimage]; exact hsub hz
    obtain ⟨p, hp⟩ := GP.gmap_surjective_Icc (hmem x (Set.mem_insert _ _))
    obtain ⟨q, hq⟩ := GP.gmap_surjective_Icc (hmem y (Set.mem_insert_of_mem _ rfl))
    obtain ⟨c, hc⟩ := h p q
    have h1 := gmap_isLUBIn_iff.1 hc
    rw [Set.image_pair, hp, hq, ← Set.image_pair] at h1
    have h2 := h1.of_image g
    rw [affIso_preimage] at h2
    exact ⟨_, h2⟩

end GPSup

section Rep

variable {M : Type u} [EffectAlgebra M] [EffectModule I M]

/-- `e : M → W` represents the convex effect algebra `M` as the interval
`[0,u]` of the ordered vector space `W`: an order isomorphism onto `[0,u]`
that preserves and reflects `⊥` and preserves `⋁`, `1` and scalars. -/
structure IsUnitRep {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W]
    (u : W) (e : M → W) : Prop where
  le_iff : ∀ a b : M, e a ≤ e b ↔ a ≤ b
  nonneg : ∀ a, 0 ≤ e a
  le_unit : ∀ a, e a ≤ u
  surj : ∀ w, 0 ≤ w → w ≤ u → ∃ a, e a = w
  perp_iff : ∀ a b : M, Perp a b ↔ e a + e b ≤ u
  add : ∀ (a b : M) (h : Perp a b), e (ovee a b h) = e a + e b
  one : e 1 = u
  smul : ∀ (l : I) (a : M), e (l • a) = (l : ℝ) • e a

theorem gp_isUnitRep : IsUnitRep (GP.gunit : GP.Vec M) (GP.gmap : M → GP.Vec M) where
  le_iff _ _ := gmap_le_gmap_iff
  nonneg := GP.gmap_nonneg
  le_unit := GP.gmap_le_gunit
  surj _ h0 h1 := GP.gmap_surjective_Icc ⟨h0, h1⟩
  perp_iff _ _ := gmap_perp_iff
  add _ _ h := GP.gmap_ovee h
  one := rfl
  smul := GP.gmap_smul

variable {W : Type u} [AddCommGroup W] [Module ℝ W] [PartialOrder W] {u : W} {e : M → W}

theorem IsUnitRep.injective (he : IsUnitRep u e) : Function.Injective e := fun a b h =>
  le_antisymm ((he.le_iff a b).1 h.le) ((he.le_iff b a).1 h.ge)

/-- Composing with a linear order isomorphism. -/
theorem IsUnitRep.comp (he : IsUnitRep u e) {W' : Type u} [AddCommGroup W'] [Module ℝ W']
    [PartialOrder W'] (g : W →ₗ[ℝ] W') (hg : Function.Surjective g)
    (hle : ∀ v w, g v ≤ g w ↔ v ≤ w) : IsUnitRep (g u) (g ∘ e) where
  le_iff a b := (hle _ _).trans (he.le_iff a b)
  nonneg a := by rw [← map_zero g]; exact (hle _ _).2 (he.nonneg a)
  le_unit a := (hle _ _).2 (he.le_unit a)
  surj w h0 h1 := by
    obtain ⟨v, rfl⟩ := hg w
    rw [← map_zero g, hle] at h0
    obtain ⟨a, rfl⟩ := he.surj v h0 ((hle _ _).1 h1)
    exact ⟨a, rfl⟩
  perp_iff a b := by
    rw [he.perp_iff, ← hle]; simp only [Function.comp, map_add]
  add a b h := by simp only [Function.comp, he.add a b h, map_add]
  one := by simp only [Function.comp, he.one]
  smul l a := by simp only [Function.comp, he.smul l a, map_smul]

/-- Suprema in `M` are suprema relative to `[0,u]`. -/
theorem IsUnitRep.relLUB (he : IsUnitRep u e) {S : Set M} {s : M} (hs : IsLUB S s) :
    0 ≤ e s ∧ e s ≤ u ∧ (∀ a ∈ S, e a ≤ e s) ∧
      ∀ w, 0 ≤ w → w ≤ u → (∀ a ∈ S, e a ≤ w) → e s ≤ w := by
  refine ⟨he.nonneg s, he.le_unit s, fun a ha => (he.le_iff a s).2 (hs.1 ha), ?_⟩
  intro w h0 h1 hw
  obtain ⟨t, rfl⟩ := he.surj w h0 h1
  exact (he.le_iff s t).2 (hs.2 fun a ha => (he.le_iff a t).1 (hw a ha))

end Rep

section Topology

variable {X : Type u} [TopologicalSpace X]

/-- `g` is a supremum of `S` relative to `[0,1]_{C(X)}`. -/
def RelSup (S : Set C(X, ℝ)) (g : C(X, ℝ)) : Prop :=
  0 ≤ g ∧ g ≤ 1 ∧ (∀ f ∈ S, f ≤ g) ∧ ∀ w, 0 ≤ w → w ≤ 1 → (∀ f ∈ S, f ≤ w) → g ≤ w

/-- The topological core of "`C(Φ)` bounded ω-complete (directed complete)
⟹ `Φ` basically (extremally) disconnected" (proof of OAP 66): if the
functions in `S` are `≤ 1`, vanish off the open `U`, and reach `1` at every
point of `U`, then a relative supremum `g` of `S` is `1` on `cl U` and `0`
off it (Urysohn), so `cl U = {g > 1/2}` is open. -/
theorem isOpen_closure_of_relSup [CompactSpace X] [T2Space X] {U : Set X} (S : Set C(X, ℝ))
    (hS : ∀ f ∈ S, (∀ x, f x ≤ 1) ∧ ∀ x ∉ U, f x = 0)
    (hS1 : ∀ x ∈ U, ∃ f ∈ S, f x = 1) {g : C(X, ℝ)} (hg : RelSup S g) :
    IsOpen (closure U) := by
  obtain ⟨hg0, hg1, hgub, hgle⟩ := hg
  have hU1 : ∀ x ∈ U, g x = 1 := fun x hx => by
    obtain ⟨f, hf, hfx⟩ := hS1 x hx
    refine le_antisymm (ContinuousMap.le_def.1 hg1 x) ?_
    rw [← hfx]; exact ContinuousMap.le_def.1 (hgub f hf) x
  have hcl1 : closure U ⊆ {x | g x = 1} :=
    closure_minimal hU1 (isClosed_eq g.continuous continuous_const)
  have hout : ∀ x ∉ closure U, g x = 0 := by
    intro x hx
    obtain ⟨h, hh0, hh1, hh⟩ := exists_continuous_zero_one_of_isClosed isClosed_singleton
      isClosed_closure (Set.disjoint_singleton_left.2 hx)
    have hle : g ≤ h := by
      refine hgle h (ContinuousMap.le_def.2 fun y => (hh y).1)
        (ContinuousMap.le_def.2 fun y => (hh y).2) fun f hf => ContinuousMap.le_def.2 fun y => ?_
      by_cases hy : y ∈ U
      · rw [hh1 (subset_closure hy)]; exact (hS f hf).1 y
      · rw [(hS f hf).2 y hy]; exact (hh y).1
    refine le_antisymm ?_ (ContinuousMap.le_def.1 hg0 x)
    have := ContinuousMap.le_def.1 hle x
    rwa [hh0 (Set.mem_singleton x)] at this
  have heq : closure U = {x | 1 / 2 < g x} := by
    ext x
    constructor
    · intro hx
      show 1 / 2 < g x
      rw [hcl1 hx]; norm_num
    · intro hx
      by_contra hc
      have : g x = 0 := hout x hc
      have hx' : (1 : ℝ) / 2 < g x := hx
      rw [this] at hx'
      norm_num at hx'
  rw [heq]
  exact isOpen_lt continuous_const g.continuous

/-- If `[0,1]_{C(X)}` has relative suprema of increasing sequences, `X` is
basically disconnected: for the cozero set `U = {f ≠ 0}` use
`hₙ = min(n·|f|, 1)`. -/
theorem basicallyDisconnected_of_relSup [CompactSpace X] [T2Space X]
    (hω : ∀ h : ℕ → C(X, ℝ), Monotone h → (∀ n, 0 ≤ h n ∧ h n ≤ 1) →
      ∃ g, RelSup (Set.range h) g) : BasicallyDisconnected X := by
  intro f
  let h : ℕ → C(X, ℝ) := fun n =>
    ⟨fun x => min ((n : ℝ) * |f x|) 1,
      (continuous_const.mul (continuous_abs.comp f.continuous)).min continuous_const⟩
  have hmono : Monotone h := fun m n hmn => ContinuousMap.le_def.2 fun x =>
    min_le_min_right _ (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (abs_nonneg _))
  obtain ⟨g, hg⟩ := hω h hmono fun n =>
    ⟨ContinuousMap.le_def.2 fun x => le_min (by positivity) zero_le_one,
      ContinuousMap.le_def.2 fun x => min_le_right _ _⟩
  refine isOpen_closure_of_relSup (Set.range h) ?_ ?_ hg
  · rintro _ ⟨n, rfl⟩
    refine ⟨fun x => min_le_right _ _, fun x hx => ?_⟩
    have hx0 : f x = 0 := by simpa using hx
    show min ((n : ℝ) * |f x|) 1 = 0
    rw [hx0, abs_zero, mul_zero, min_eq_left zero_le_one]
  · intro x hx
    have hpos : 0 < |f x| := abs_pos.2 hx
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / |f x|)
    refine ⟨h n, ⟨n, rfl⟩, ?_⟩
    show min ((n : ℝ) * |f x|) 1 = 1
    refine min_eq_right ?_
    rw [div_le_iff₀ hpos] at hn
    exact hn

/-- If `[0,1]_{C(X)}` has relative suprema of directed sets, `X` is
extremally disconnected: for open `U` use all `f ∈ [0,1]_{C(X)}` vanishing
off `U`. -/
theorem extremallyDisconnected_of_relSup [CompactSpace X] [T2Space X]
    (hd : ∀ S : Set C(X, ℝ), (∀ f ∈ S, 0 ≤ f ∧ f ≤ 1) → S.Nonempty → DirectedOn (· ≤ ·) S →
      ∃ g, RelSup S g) : ExtremallyDisconnected X := by
  refine ⟨fun U hU => ?_⟩
  let S : Set C(X, ℝ) := {f | 0 ≤ f ∧ f ≤ 1 ∧ ∀ x ∉ U, f x = 0}
  obtain ⟨g, hg⟩ := hd S (fun f hf => ⟨hf.1, hf.2.1⟩) ⟨0, le_rfl, zero_le_one, fun _ _ => rfl⟩
    (fun f hf f' hf' => ⟨f ⊔ f', ⟨le_sup_of_le_left hf.1, sup_le hf.2.1 hf'.2.1, fun x hx => by
      rw [ContinuousMap.sup_apply, hf.2.2 x hx, hf'.2.2 x hx, max_self]⟩,
      le_sup_left, le_sup_right⟩)
  refine isOpen_closure_of_relSup S (fun f hf => ⟨fun x => ContinuousMap.le_def.1 hf.2.1 x,
    hf.2.2⟩) ?_ hg
  intro x hx
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.2 fun h => h hx)
  exact ⟨f, ⟨ContinuousMap.le_def.2 fun y => (hf y).1, ContinuousMap.le_def.2 fun y => (hf y).2,
    fun y hy => hf0 hy⟩, hf1 (Set.mem_singleton x)⟩

end Topology

section Mult

attribute [local instance] unitIntervalEffectMonoid

variable {M : Type u} [EffectMonoid M] [EffectModule I M]
variable {X : Type u} [TopologicalSpace X] {E : M → C(X, ℝ)}

/-- The print's estimate `d(f∗g, f∗h) ≤ f∗d(g,h) ≤ d(g,h)`, evaluated at a
point (proof of OAP 66).  The print writes `f∗(g∨h) ≤ (f∗g)∨(f∗h)` and
`f∗(g∧h) ≥ (f∗g)∧(f∗h)`; monotonicity of `∗` gives the *reverse*
inequalities, which are the ones the estimate needs. -/
theorem IsUnitRep.dist_mul (hE : IsUnitRep (1 : C(X, ℝ)) E) (a c c' : M) (x : X) :
    |E (a * c) x - E (a * c') x| ≤ |E c x - E c' x| := by
  have hmono : ∀ {p q : M}, p ≤ q → E p x ≤ E q x := fun h =>
    ContinuousMap.le_def.1 ((hE.le_iff _ _).2 h) x
  obtain ⟨m, hm⟩ := hE.surj (E c ⊓ E c') (le_inf (hE.nonneg c) (hE.nonneg c'))
    (inf_le_left.trans (hE.le_unit c))
  obtain ⟨m2, hm2⟩ := hE.surj (E c ⊔ E c') (le_sup_of_le_left (hE.nonneg c))
    (sup_le (hE.le_unit c) (hE.le_unit c'))
  obtain ⟨d, hd⟩ := hE.surj (E c ⊔ E c' - E c ⊓ E c') (sub_nonneg.2 inf_le_sup)
    ((sub_le_self _ (le_inf (hE.nonneg c) (hE.nonneg c'))).trans
      (sup_le (hE.le_unit c) (hE.le_unit c')))
  have hmd : E m + E d = E m2 := by rw [hm, hd, hm2]; abel
  have hp : Perp m d := (hE.perp_iff m d).2 (by rw [hmd]; exact hE.le_unit m2)
  have hsum : m ⋎ d = m2 := hE.injective (by rw [oplus_eq hp, hE.add, hmd])
  have hmc : m ≤ c := (hE.le_iff _ _).1 (by rw [hm]; exact inf_le_left)
  have hmc' : m ≤ c' := (hE.le_iff _ _).1 (by rw [hm]; exact inf_le_right)
  have hcm : c ≤ m2 := (hE.le_iff _ _).1 (by rw [hm2]; exact le_sup_left)
  have hcm' : c' ≤ m2 := (hE.le_iff _ _).1 (by rw [hm2]; exact le_sup_right)
  obtain ⟨hp', e'⟩ := mul_oplus a hp
  have hhi : E (a * m2) x = E (a * m) x + E (a * d) x := by
    rw [← hsum, e', oplus_eq hp', hE.add, ContinuousMap.add_apply]
  have hd' : E (a * d) x ≤ E d x := hmono (emul_le_right a d)
  have hdx : E d x = max (E c x) (E c' x) - min (E c x) (E c' x) := by
    rw [hd, ContinuousMap.sub_apply, ContinuousMap.sup_apply, ContinuousMap.inf_apply]
  have h1 := hmono (emul_le_emul_left a hmc)
  have h2 := hmono (emul_le_emul_left a hmc')
  have h3 := hmono (emul_le_emul_left a hcm)
  have h4 := hmono (emul_le_emul_left a hcm')
  rw [max_sub_min_eq_abs'] at hdx
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The multiplication of `M`, transported to `[0,1]_{C(X)}`, is the
pointwise product (proof of OAP 66, after [Riesz spaces, Lemma 5.26]): at a
point `x`, with `α = g(x)`, `f ∗ (α·1) = α·f` by OAP 63, and
`|(f∗g)(x) - (f∗(α·1))(x)| ≤ |g(x) - α| = 0`. -/
theorem IsUnitRep.mul_apply [OmegaComplete M] (hE : IsUnitRep (1 : C(X, ℝ)) E) (a c : M)
    (x : X) : E (a * c) x = E a x * E c x := by
  have h0 : 0 ≤ E c x := ContinuousMap.le_def.1 (hE.nonneg c) x
  have h1 : E c x ≤ 1 := ContinuousMap.le_def.1 (hE.le_unit c) x
  let ι : I := ⟨E c x, h0, h1⟩
  have hc' : E (ι • (1 : M)) x = E c x := by
    rw [hE.smul, hE.one]; simp [ι]
  have hac' : E (a * (ι • (1 : M))) x = E c x * E a x := by
    rw [← (oap63 ι a 1).2, emul_one, hE.smul]; rfl
  have := hE.dist_mul a c (ι • 1) x
  rw [hc', hac', sub_self, abs_zero] at this
  rw [mul_comm]
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- The effect monoid morphism `M → [0,1]_{C(X)}` of a representation. -/
def IsUnitRep.toHom [OmegaComplete M] (hE : IsUnitRep (1 : C(X, ℝ)) E) :
    @EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1) _ (unitIntervalEffectMonoid C(X, ℝ)) :=
  letI := unitIntervalEffectMonoid C(X, ℝ)
  { toFun := fun a => ⟨E a, hE.nonneg a, hE.le_unit a⟩
    perp_map := fun {a b} h => (show E a + E b ≤ 1 from (hE.perp_iff a b).1 h)
    ovee_map := fun {a b} h => Subtype.ext (hE.add a b h)
    map_one := Subtype.ext hE.one
    map_mul := fun a b => Subtype.ext (ContinuousMap.ext fun x => hE.mul_apply a b x) }

theorem IsUnitRep.toHom_apply [OmegaComplete M] (hE : IsUnitRep (1 : C(X, ℝ)) E) (a : M) :
    ((hE.toHom.toFun a : Set.Icc (0 : C(X, ℝ)) 1) : C(X, ℝ)) = E a := rfl

theorem IsUnitRep.toHom_isIso [OmegaComplete M] (hE : IsUnitRep (1 : C(X, ℝ)) E) :
    @EMIsIso M _ _ (unitIntervalEffectMonoid C(X, ℝ)) hE.toHom := by
  refine (@oap8_isIso_iff M _ _ (unitIntervalEffectMonoid C(X, ℝ)) hE.toHom).2 ⟨?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := hE.surj y y.2.1 y.2.2
    exact ⟨a, Subtype.ext ha⟩
  · intro a b h
    exact (hE.le_iff a b).1 ((oap3_le_iff C(X, ℝ) 1 zero_le_one _ _).1 h)

/-- ω-completeness of `M` gives relative suprema of increasing sequences in
`[0,1]_{C(X)}`. -/
theorem IsUnitRep.relSup_omega [OmegaComplete M] (hE : IsUnitRep (1 : C(X, ℝ)) E)
    (h : ℕ → C(X, ℝ)) (hh : Monotone h) (hmem : ∀ n, 0 ≤ h n ∧ h n ≤ 1) :
    ∃ g, RelSup (Set.range h) g := by
  choose p hp using fun n => hE.surj (h n) (hmem n).1 (hmem n).2
  have hpm : Monotone p := fun m n hmn => (hE.le_iff _ _).1 (by rw [hp, hp]; exact hh hmn)
  obtain ⟨s, hs⟩ := OmegaComplete.exists_isLUB p hpm
  obtain ⟨h0, h1, hub, hle⟩ := hE.relLUB hs
  refine ⟨E s, h0, h1, ?_, fun w hw0 hw1 hw => hle w hw0 hw1 ?_⟩
  · rintro _ ⟨n, rfl⟩; rw [← hp]; exact hub _ ⟨n, rfl⟩
  · rintro _ ⟨n, rfl⟩; rw [hp]; exact hw _ ⟨n, rfl⟩

/-- Directed completeness of `M` gives relative suprema of directed sets in
`[0,1]_{C(X)}`. -/
theorem IsUnitRep.relSup_directed [OmegaComplete M] [DirectedComplete M]
    (hE : IsUnitRep (1 : C(X, ℝ)) E) (S : Set C(X, ℝ)) (hS : ∀ f ∈ S, 0 ≤ f ∧ f ≤ 1)
    (hne : S.Nonempty) (hd : DirectedOn (· ≤ ·) S) : ∃ g, RelSup S g := by
  let T : Set M := E ⁻¹' S
  have hT : ∀ f ∈ S, ∃ a ∈ T, E a = f := fun f hf => by
    obtain ⟨a, ha⟩ := hE.surj f (hS f hf).1 (hS f hf).2
    exact ⟨a, by simp only [T, Set.mem_preimage, ha]; exact hf, ha⟩
  obtain ⟨f0, hf0⟩ := hne
  obtain ⟨a0, ha0, -⟩ := hT f0 hf0
  obtain ⟨s, hs⟩ := DirectedComplete.exists_isLUB T ⟨⟨a0, ha0⟩, fun a ha b hb => by
    obtain ⟨f, hf, haf, hbf⟩ := hd _ ha _ hb
    obtain ⟨c, hc, rfl⟩ := hT f hf
    exact ⟨c, hc, (hE.le_iff _ _).1 haf, (hE.le_iff _ _).1 hbf⟩⟩
  obtain ⟨h0, h1, hub, hle⟩ := hE.relLUB hs
  refine ⟨E s, h0, h1, fun f hf => ?_, fun w hw0 hw1 hw => hle w hw0 hw1 fun a ha => hw _ ha⟩
  obtain ⟨a, ha, rfl⟩ := hT f hf
  exact hub a ha

end Mult

section OAP66

attribute [local instance] unitIntervalEffectMonoid

variable {M : Type u} [EffectMonoid M] [EffectModule I M]

/-- **OAP 66** (`thm:convexextremallydisconnected`, first.tex:2489, Theorem):
a convex ω-complete effect monoid `M` is isomorphic (as an effect monoid, and
compatibly with the convex structure) to `[0,1]_{C(X)}` for a *compact*
Hausdorff basically disconnected space `X`; if `M` is directed complete, `X`
is extremally disconnected.

**Waits on OAP 37**: that `M` is a lattice (`FloorCeiling.lean`, not
importable here) is the hypothesis `oap37`.  The print omits "compact"; the
proof produces the Yosida spectrum, which is compact.

Proof as printed: `M ≅ [0,1]_V` with `V = GP.Vec M` (OAP 62); `V` is a lattice
(`gp_sup`, from `oap37`), bounded ω-complete (OAP 60), Archimedean (OAP 61),
norm-complete (Wright's lemma, `wright_normComplete`, cited in the print);
Yosida (OAP 64) gives `V ≅ C(Φ)`; the transported product is pointwise
(`IsUnitRep.mul_apply`); `Φ` is basically/extremally disconnected
(`basicallyDisconnected_of_relSup`, `extremallyDisconnected_of_relSup` —
the print's "Note …" cites Gillman–Jerison; only the needed direction is
proved). -/
theorem oap66 [OmegaComplete M] (oap37 : ∀ a b : M, ∃ c, IsLUB ({a, b} : Set M) c) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
      (f : EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1)), EMIsIso f ∧
      (∀ (l : I) (a : M), (f.toFun (l • a) : C(X, ℝ)) = (l : ℝ) • (f.toFun a : C(X, ℝ))) ∧
      BasicallyDisconnected X ∧ (DirectedComplete M → ExtremallyDisconnected X) := by
  let _ : Lattice (GP.Vec M) := vecLattice (gp_sup oap37)
  have hA : OUSArchimedean (GP.Vec M) := gp_archimedean
  have hC : OUSNormComplete (GP.Vec M) := wright_normComplete (oap60_omega.1 gp_omegaComplete)
  have hE' := (gp_isUnitRep (M := M)).comp (yosidaMap (GP.Vec M))
    (oap64_yosida hA hC).1.2 (fun v w => yosidaMap_le_iff hA)
  have hu : yosidaMap (GP.Vec M) GP.gunit = 1 := yosidaMap_unit
  rw [hu] at hE'
  refine ⟨YosidaSpectrum (GP.Vec M), inferInstance, inferInstance, inferInstance, hE'.toHom,
    hE'.toHom_isIso, fun l a => hE'.smul l a,
    basicallyDisconnected_of_relSup hE'.relSup_omega, fun hD => ?_⟩
  exact extremallyDisconnected_of_relSup hE'.relSup_directed

end OAP66

/-! ## OAP 64, 65, 67

**OAP 64** (`prop:yosida`, first.tex:2465, Theorem; Yosida) is
`Papers.OAP.oap64_yosida` in `Yosida.lean`.

**OAP 65** (first.tex:2474, Remark): the dual equivalence between compact
Hausdorff spaces and lattice-ordered norm-complete Archimedean order unit
spaces is cited (B. Westerbaan, *Yosida duality*); not formalised.

**OAP 67** (first.tex:2551, Remark): OAP 66 can alternatively be proved with
Kadison's representation theorem, after extending the product of `[0,1]_V` to
`V` (cited); not formalised. -/

end

end Papers.OAP
